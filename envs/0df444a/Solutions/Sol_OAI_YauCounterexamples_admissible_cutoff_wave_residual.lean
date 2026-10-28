-- Prove2me | solution 1 for OAI.YauCounterexamples.admissible_cutoff_wave_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:00:25.014704+00:00
-- url     : https://prove2.me/submissions/253dd5a4-56b7-4158-83c4-62fc836333cb

import Mathlib
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_all_admissible_generated_gaussian
import Theorems.Thm_OAI_YauCounterexamples_cutoff_polynomial_wave_residual_bound
import Theorems.Thm_OAI_YauCounterexamples_generated_wave_uniform_jets

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_MultilinearPolynomial
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiff_directionalJet {f : E → F} (hf : ContDiff ℝ ∞ f) (l : List E) :
    ContDiff ℝ ∞ (directionalJet l f) := by
  induction l with
  | nil => exact hf
  | cons v l ih =>
    exact (ih.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const

lemma directionalJet_swap {f : E → F} (hf : ContDiff ℝ ∞ f)
    (a b : E) (l : List E) :
    directionalJet (a :: b :: l) f = directionalJet (b :: a :: l) f := by
  have hg := contDiff_directionalJet hf l
  have hgd := hg.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)
  ext x
  have ha := fderiv_clm_apply (hgd.differentiable (by simp) x) (differentiableAt_const (c := b))
  have hb := fderiv_clm_apply (hgd.differentiable (by simp) x) (differentiableAt_const (c := a))
  simp only [directionalJet_cons, ha, hb, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  simpa using (hg.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)))) a b

lemma directionalJet_perm {f : E → F} (hf : ContDiff ℝ ∞ f)
    {l₁ l₂ : List E} (h : l₁.Perm l₂) : directionalJet l₁ f = directionalJet l₂ f := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [directionalJet_cons, ih]
  | swap a b l => exact directionalJet_swap hf b a l
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

lemma iteratedFDeriv_eq_directionalJet {f : E → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → E) (x : E) :
    iteratedFDeriv ℝ n f x v = directionalJet (List.ofFn v) f x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hd := hf.differentiable_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) x
    rw [hd.iteratedFDeriv_succ_apply_left', List.ofFn_succ, directionalJet_cons]
    congr 2
    funext y
    exact ih (Fin.tail v) y

theorem smooth_iteratedFDeriv_comp_perm {f : E → F} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (v : Fin n → E) (σ : Equiv.Perm (Fin n)) (x : E) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  rw [iteratedFDeriv_eq_directionalJet hf, iteratedFDeriv_eq_directionalJet hf,
    directionalJet_perm hf (σ.ofFn_comp_perm v)]

theorem iteratedFDeriv_finiteTaylorFunction [CompleteSpace F]
    {f : E → F} (hf : ContDiff ℝ ∞ f) (N k : ℕ) (hk : k < N) :
    iteratedFDeriv ℝ k (finiteTaylorFunction f N) 0 = iteratedFDeriv ℝ k f 0 := by
  classical
  let p : FormalMultilinearSeries ℝ E F := fun j => if j < N then
    (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j f 0 else 0
  have hp : HasFiniteFPowerSeriesOnBall (finiteTaylorFunction f N) p 0 N ⊤ := by
    apply HasFiniteFPowerSeriesOnBall.mk'
    · intro j hj
      simp [p, not_lt.mpr hj]
    · simp
    · intro y _
      simp only [finiteTaylorFunction, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      simp [p, Finset.mem_range.mp hj]
  ext v
  rw [hp.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace]
  have heq (σ : Equiv.Perm (Fin k)) : p k (fun i => v (σ i)) =
      (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f 0 v := by
    simp only [p, ite_eq_left hk, smul_apply]
    rw [show (fun i => v (σ i)) = v ∘ σ from rfl,
      smooth_iteratedFDeriv_comp_perm hf]
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero k


end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

open MvPolynomial
variable {σ : Type*}

variable [Fintype σ]

theorem contDiff_realPolyEval (p : MvPolynomial σ ℂ) : ContDiff ℝ ∞ (realPolyEval p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [show realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c by funext x; exact realPolyEval_C c x]
    exact contDiff_const
  | add p q hp hq =>
    rw [show realPolyEval (p + q) = fun x => realPolyEval p x + realPolyEval q x by funext x; exact realPolyEval_add p q x]
    exact hp.add hq
  | mul_X p i hp =>
    have hx : ContDiff ℝ ∞ (fun x : σ → ℝ => (x i : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ).contDiff
    rw [show realPolyEval (p * X i) = fun x => realPolyEval p x * (x i : ℂ) by funext x; simp]
    exact hp.mul hx

theorem fderiv_realPolyEval (p : MvPolynomial σ ℂ) (x v : σ → ℝ) :
    fderiv ℝ (realPolyEval p) x v =
      ∑ i, (v i : ℂ) * realPolyEval (pderiv i p) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
    have heq : realPolyEval (C c : MvPolynomial σ ℂ) = fun _ => c := by ext x; exact realPolyEval_C c x
    rw [heq]
    simp
  | add p q hp hq =>
    have h := fderiv_add ((contDiff_realPolyEval p).differentiable (by simp) x)
      ((contDiff_realPolyEval q).differentiable (by simp) x)
    rw [show realPolyEval (p + q) = realPolyEval p + realPolyEval q by ext; simp, h]
    simp only [add_apply, hp, hq, map_add,
      realPolyEval_add, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have hcoord : HasFDerivAt (fun x : σ → ℝ => (x j : ℂ))
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_apply j x)
    rw [show realPolyEval (p * X j) = fun x => realPolyEval p x * (x j : ℂ) by ext; simp,
      fderiv_fun_mul ((contDiff_realPolyEval p).differentiable (by simp) x)
        hcoord.differentiableAt, hcoord.fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply,
      smul_eq_mul, hp, pderiv_mul, realPolyEval_add, realPolyEval_mul, realPolyEval_X,
      pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib]
    have hif (i : σ) : realPolyEval (if j = i then 1 else 0) x =
        if j = i then 1 else 0 := by split_ifs <;> simp
    simp only [hif, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [← mul_assoc, ← Finset.sum_mul]
    ring

theorem fderiv_realPolyEval_eq (p : MvPolynomial σ ℂ) :
    fderiv ℝ (realPolyEval p) =
      ∑ i, realPolyDerivEmbed i ∘ realPolyEval (pderiv i p) := by
  classical
  ext x v
  simp [fderiv_realPolyEval]

theorem realPolyEval_jet_zero_of_coeff (k : ℕ) (p : MvPolynomial σ ℂ)
    (hp : ∀ d : σ →₀ ℕ, d.degree < k + 1 → p.coeff d = 0) :
    iteratedFDeriv ℝ k (realPolyEval p) 0 = 0 := by
  classical
  induction k generalizing p with
  | zero =>
    have h₀ : constantCoeff p = 0 := hp 0 (by simp)
    ext v
    simpa [realPolyEval] using h₀
  | succ k ih =>
    have hp' (i : σ) : ∀ d : σ →₀ ℕ, d.degree < k + 1 → (pderiv i p).coeff d = 0 := by
      intro d hd
      rw [coeff_pderiv, hp (d + Finsupp.single i 1), zero_mul]
      simpa only [map_add, Finsupp.degree_single, Nat.add_lt_add_iff_right] using hd
    have hz (i : σ) := ih (pderiv i p) (hp' i)
    have hcont (i : σ) : ContDiff ℝ (k : ℕ∞ω)
        (realPolyDerivEmbed i ∘ realPolyEval (pderiv i p)) :=
      ((realPolyDerivEmbed i).contDiff.comp (contDiff_realPolyEval _)).of_le
        (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))
    have hf : iteratedFDeriv ℝ k (fderiv ℝ (realPolyEval p)) 0 = 0 := by
      rw [fderiv_realPolyEval_eq, iteratedFDeriv_sum_apply (fun i _ => (hcont i).contDiffAt)]
      apply Finset.sum_eq_zero
      intro i _
      rw [(realPolyDerivEmbed i).iteratedFDeriv_comp_left
        (contDiff_realPolyEval _).contDiffAt
          (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))), hz i]
      ext m v
      simp
    apply norm_eq_zero.mp
    rw [← norm_iteratedFDeriv_fderiv, hf, norm_zero]


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem realPolyEval_multilinearPolynomial {n : ℕ}
    (B : (σ → ℝ) [×n]→L[ℝ] ℂ) (x : σ → ℝ) :
    realPolyEval (multilinearPolynomial B) x = B (fun _ => x) := by
  classical
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hB : B (fun _ => x) = ∑ a : Fin n → σ,
      (∏ i, x (a i)) • B (fun i => Pi.single (a i) 1) := by
    conv_lhs => rw [hx]
    rw [B.map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact B.map_smul_univ _ _
  rw [hB]
  simp only [multilinearPolynomial, realPolyEval, map_sum, map_mul, eval_C, map_prod, eval_X]
  apply Finset.sum_congr rfl
  intro a _
  rw [Complex.real_smul, Complex.ofReal_prod]
  exact mul_comm _ _

theorem realPolyEval_realTaylorPolynomial (f : (σ → ℝ) → ℂ) (N : ℕ) (x : σ → ℝ) :
    realPolyEval (realTaylorPolynomial f N) x = finiteTaylorFunction f N x := by
  simp only [realTaylorPolynomial, realPolyEval, map_sum, map_mul, eval_C,
    finiteTaylorFunction]
  apply Finset.sum_congr rfl
  intro j _
  rw [show MvPolynomial.eval (fun i => (x i : ℂ))
    (multilinearPolynomial (iteratedFDeriv ℝ j f 0)) =
      realPolyEval (multilinearPolynomial (iteratedFDeriv ℝ j f 0)) x from rfl,
    realPolyEval_multilinearPolynomial, Complex.real_smul]
  simp

theorem realTaylorPolynomial_jet {f : (σ → ℝ) → ℂ} (hf : ContDiff ℝ ∞ f)
    (N k : ℕ) (hk : k < N) :
    iteratedFDeriv ℝ k (realPolyEval (realTaylorPolynomial f N)) 0 =
      iteratedFDeriv ℝ k f 0 := by
  rw [show realPolyEval (realTaylorPolynomial f N) = finiteTaylorFunction f N from
    funext (realPolyEval_realTaylorPolynomial f N)]
  exact iteratedFDeriv_finiteTaylorFunction hf N k hk



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_BoundedDegreeMonomials
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SmoothJetZero
lemma mono {f : E → F} {N M : ℕ} (h : SmoothJetZero f N) (hMN : M ≤ N) :
    SmoothJetZero f M := fun k hk => h k (hk.trans_le hMN)
lemma zero (N : ℕ) : SmoothJetZero (0 : E → F) N := by
  intro k _
  exact congrFun (iteratedFDeriv_zero (𝕜 := ℝ) (n := k)) 0
lemma order_zero (f : E → F) : SmoothJetZero f 0 := by intro k hk; omega
lemma add {f g : E → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (hfj : SmoothJetZero f N) (hgj : SmoothJetZero g N) :
    SmoothJetZero (f + g) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_add_apply (hf.of_le hle).contDiffAt (hg.of_le hle).contDiffAt,
    hfj k hk, hgj k hk, add_zero]
lemma sum {ι : Type*} (s : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ s, ContDiff ℝ ∞ (f i)) {N : ℕ}
    (hj : ∀ i ∈ s, SmoothJetZero (f i) N) : SmoothJetZero (∑ i ∈ s, f i) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_sum_apply (fun i hi => ((hf i hi).of_le hle).contDiffAt)]
  exact Finset.sum_eq_zero (fun i hi => hj i hi k hk)

lemma mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f g : E → A} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {N M : ℕ} (hfj : SmoothJetZero f N) (hgj : SmoothJetZero g M) :
    SmoothJetZero (fun x => f x * g x) (N + M) := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  have hb := norm_iteratedFDeriv_mul_le hf hg (0 : E) hle
  have hz : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i f 0‖ * ‖iteratedFDeriv ℝ (k - i) g 0‖ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ k := by simpa using Finset.mem_range.mp hi
    by_cases h : i < N
    · simp [hfj i h]
    · simp [hgj (k - i) (by omega)]
  rw [hz] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

lemma mul_right {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    {f : E → A} (hf : ContDiff ℝ ∞ f) (g : E → A) (hg : ContDiff ℝ ∞ g)
    {N : ℕ} (h : SmoothJetZero f N) : SmoothJetZero (fun x => f x * g x) N := by
  simpa using h.mul hf hg (order_zero g)

end SmoothJetZero

end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
section PolynomialWaves
open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem waveDirectionalDerivative_homogeneous (z : σ → ℂ)
    {f : MvPolynomial σ ℂ} {d : ℕ} (hf : f.IsHomogeneous d) :
    (waveDirectionalDerivative z f).IsHomogeneous (d - 1) := by
  rw [waveDirectionalDerivative_apply]
  apply IsHomogeneous.sum
  intro i _
  simpa only [← C_mul'] using hf.pderiv.C_mul (z i)

theorem waveDirectionalDerivative_degree_zero (z : σ → ℂ)
    {f : MvPolynomial σ ℂ} (hf : f.IsHomogeneous 0) :
    waveDirectionalDerivative z f = 0 := by
  rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hf
  rw [hf, waveDirectionalDerivative_C]

theorem wavePrimitiveTerm_homogeneous (z : σ → ℂ)
    (ℓ : MvPolynomial σ ℂ) (hℓ : ℓ.IsHomogeneous 1)
    (d j : ℕ) (f : MvPolynomial σ ℂ) (hf : f.IsHomogeneous d) :
    (wavePrimitiveTerm z ℓ d j f).IsHomogeneous (d + j + 1) := by
  induction d generalizing j f with
  | zero =>
      dsimp [wavePrimitiveTerm]
      have h := ((hℓ.pow (j + 1)).mul hf).C_mul (((j + 1 : ℕ) : ℂ)⁻¹)
      simpa only [one_mul, add_zero, zero_add, C_mul'] using h
  | succ d ih =>
      have hdf : (waveDirectionalDerivative z f).IsHomogeneous d := by
        simpa only [Nat.add_sub_cancel] using waveDirectionalDerivative_homogeneous z hf
      have h₁ : (ℓ ^ (j + 1) * f).IsHomogeneous (d + 1 + j + 1) := by
        convert (hℓ.pow (j + 1)).mul hf using 1; omega
      have h₂ : (wavePrimitiveTerm z ℓ d (j + 1)
          (waveDirectionalDerivative z f)).IsHomogeneous (d + 1 + j + 1) := by
        convert ih (j + 1) _ hdf using 1; omega
      dsimp only [wavePrimitiveTerm]
      simpa only [C_mul'] using (h₁.sub h₂).C_mul (((j + 1 : ℕ) : ℂ)⁻¹)

theorem wavePrimitiveTerm_derivative (z : σ → ℂ)
    (ℓ : MvPolynomial σ ℂ) (hℓ : waveDirectionalDerivative z ℓ = 1)
    (d j : ℕ) (f : MvPolynomial σ ℂ) (hf : f.IsHomogeneous d) :
    waveDirectionalDerivative z (wavePrimitiveTerm z ℓ d j f) = ℓ ^ j * f := by
  have hj (j : ℕ) : (((j + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hpow (j : ℕ) : waveDirectionalDerivative z (ℓ ^ (j + 1)) =
      ((j + 1 : ℕ) : ℂ) • ℓ ^ j := by
    rw [Derivation.leibniz_pow, hℓ, Nat.add_sub_cancel]
    simp [Algebra.smul_def]
  induction d generalizing j f with
  | zero =>
      rw [wavePrimitiveTerm, Derivation.map_smul, Derivation.leibniz,
        waveDirectionalDerivative_degree_zero z hf, hpow]
      simp only [smul_eq_mul, mul_zero, zero_add, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (hj j), one_smul, mul_comm]
  | succ d ih =>
      have hdf : (waveDirectionalDerivative z f).IsHomogeneous d := by
        simpa only [Nat.add_sub_cancel] using waveDirectionalDerivative_homogeneous z hf
      rw [wavePrimitiveTerm, Derivation.map_smul, map_sub, Derivation.leibniz,
        hpow, ih (j + 1) _ hdf]
      simp only [smul_eq_mul, add_sub_cancel_left]
      rw [mul_smul_comm, smul_smul, inv_mul_cancel₀ (hj j), one_smul, mul_comm]

theorem waveNormSq_pos (z : σ → ℂ) (hz : z ≠ 0) : 0 < waveNormSq z := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra! h
    exact hz (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (z j))
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

theorem waveLinearCoordinate_homogeneous (z : σ → ℂ) :
    (waveLinearCoordinate z).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i _
  simpa only [C_mul'] using (isHomogeneous_X ℂ i).C_mul
    (star (z i) / (waveNormSq z : ℂ))

theorem waveLinearCoordinate_derivative (z : σ → ℂ) (hz : z ≠ 0) :
    waveDirectionalDerivative z (waveLinearCoordinate z) = 1 := by
  have hd : (waveNormSq z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (waveNormSq_pos z hz))
  simp only [waveLinearCoordinate, map_sum, Derivation.map_smul,
    waveDirectionalDerivative_X]
  simp only [Algebra.smul_def, algebraMap_eq, ← map_mul, ← map_sum]
  rw [show (1 : MvPolynomial σ ℂ) = C 1 by simp]
  congr 1
  calc
    ∑ i, (star (z i) / (waveNormSq z : ℂ)) * z i =
        (∑ i, z i * star (z i)) / (waveNormSq z : ℂ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (waveNormSq z : ℂ) / (waveNormSq z : ℂ) := by
      congr 1
      simp only [Complex.star_def, Complex.mul_conj, waveNormSq, Complex.ofReal_sum]
    _ = 1 := div_self hd

end PolynomialWaves

section FiniteJets
open MvPolynomial
variable {σ R : Type*} [CommRing R]

namespace VanishTo

theorem zero (N : ℕ) : VanishTo (0 : MvPolynomial σ R) N := by
  intro m _
  rfl

theorem order_zero (p : MvPolynomial σ R) : VanishTo p 0 := by
  intro m hm
  omega

theorem mono {p : MvPolynomial σ R} {N M : ℕ} (hp : VanishTo p N)
    (h : M ≤ N) : VanishTo p M := fun m hm => hp m (hm.trans_le h)

theorem add {p q : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (hq : VanishTo q N) : VanishTo (p + q) N := by
  intro m hm
  rw [MvPolynomial.coeff_add, hp m hm, hq m hm, add_zero]

theorem sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial σ R} {N : ℕ}
    (h : ∀ i ∈ s, VanishTo (f i) N) : VanishTo (∑ i ∈ s, f i) N := by
  intro m hm
  simp only [coeff_sum]
  exact Finset.sum_eq_zero (fun i hi => h i hi m hm)

theorem mul {p q : MvPolynomial σ R} {N M : ℕ}
    (hp : VanishTo p N) (hq : VanishTo q M) : VanishTo (p * q) (N + M) := by
  classical
  intro m hm
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro t ht
  have ht' : t.1 + t.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp ht
  have hd : t.1.degree + t.2.degree = m.degree := by
    rw [← map_add, ht']
  by_cases h : t.1.degree < N
  · rw [hp t.1 h, zero_mul]
  · have h' : t.2.degree < M := by omega
    rw [hq t.2 h', mul_zero]

theorem mul_left {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (q : MvPolynomial σ R) : VanishTo (q * p) N := by
  simpa only [zero_add] using (order_zero q).mul hp

theorem mul_right {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (q : MvPolynomial σ R) : VanishTo (p * q) N := by
  simpa only [add_zero] using hp.mul (order_zero q)

theorem pderiv {p : MvPolynomial σ R} {N : ℕ} (hp : VanishTo p (N + 1))
    (i : σ) : VanishTo (pderiv i p) N := by
  intro m hm
  rw [coeff_pderiv, hp (m + Finsupp.single i 1), zero_mul]
  simpa only [map_add, Finsupp.degree_single, Nat.add_lt_add_iff_right] using hm

theorem of_homogeneous {p : MvPolynomial σ R} {N : ℕ} (hp : p.IsHomogeneous N) :
    VanishTo p N := fun _ hm => hp.coeff_eq_zero (ne_of_lt hm)

theorem of_constantCoeff_eq_zero {p : MvPolynomial σ R}
    (hp : constantCoeff p = 0) : VanishTo p 1 := by
  intro m hm
  have h : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
  simpa only [h, constantCoeff_eq] using hp

theorem constantCoeff_eq_zero {p : MvPolynomial σ R} {N : ℕ}
    (hp : VanishTo p N) (hN : 0 < N) : constantCoeff p = 0 := by
  exact hp 0 (by simpa using hN)

theorem remove_component {p : MvPolynomial σ R} {N : ℕ} (hp : VanishTo p N) :
    VanishTo (p - homogeneousComponent N p) (N + 1) := by
  intro m hm
  rw [coeff_sub, coeff_homogeneousComponent]
  by_cases h : m.degree = N
  · simp [h]
  · have h' : m.degree < N := by omega
    simp [h, hp m h']

theorem of_constant_and_linear {p : MvPolynomial σ R}
    (h₀ : constantCoeff p = 0) (h₁ : ∀ i, constantCoeff (MvPolynomial.pderiv i p) = 0) :
    VanishTo p 2 := by
  intro m hm
  by_cases hm₀ : m = 0
  · subst m
    exact h₀
  · have hmdeg : m.degree = 1 := by
      have hne : m.degree ≠ 0 := mt (Finsupp.degree_eq_zero_iff m).mp hm₀
      omega
    obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff m).mp hmdeg
    simpa only [constantCoeff_eq, coeff_pderiv, zero_add, Finsupp.zero_apply,
      Nat.cast_zero, mul_one] using h₁ i

end VanishTo

variable [Fintype σ] [DecidableEq σ]

theorem waveQuadratic_linearization (G : σ → σ → MvPolynomial σ R)
    (u v : σ → MvPolynomial σ R) (z : σ → R) (N : ℕ) (hN : 1 ≤ N)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hu : ∀ i, constantCoeff (u i) = z i) (hv : ∀ i, VanishTo (v i) N) :
    VanishTo (waveQuadratic G (fun i => u i + v i) - waveQuadratic G u -
      2 * ∑ i, C (z i) * v i) (N + 1) := by
  classical
  have hp (i j : σ) : VanishTo
      (G i j * (u i + v i) * (u j + v j) - G i j * u i * u j -
        if i = j then C (z i) * v i + C (z i) * v i else 0) (N + 1) := by
    have hquad : VanishTo (G i j * v i * v j) (N + 1) := by
      exact (((hv i).mul_left (G i j)).mul (hv j)).mono (by omega)
    by_cases hij : i = j
    · subst j
      have hbase : VanishTo (G i i * u i - C (z i)) 1 := by
        apply VanishTo.of_constantCoeff_eq_zero
        simp [hG, hu]
      have hlin : VanishTo ((G i i * u i - C (z i)) * v i) (N + 1) := by
        simpa only [Nat.add_comm 1] using hbase.mul (hv i)
      convert (hlin.add hlin).add hquad using 1
      all_goals try with_reducible_and_instances rfl
      simp only [ite_true]
      ring
    · have hg : VanishTo (G i j) 1 := by
        apply VanishTo.of_constantCoeff_eq_zero
        simp [hG, hij]
      have hfirst : VanishTo (G i j * u i * v j) (N + 1) := by
        simpa only [Nat.add_comm 1] using (hg.mul_right (u i)).mul (hv j)
      have hsecond : VanishTo (G i j * u j * v i) (N + 1) := by
        simpa only [Nat.add_comm 1] using (hg.mul_right (u j)).mul (hv i)
      convert (hfirst.add hsecond).add hquad using 1
      all_goals try with_reducible_and_instances rfl
      simp only [hij, ite_false]
      ring
  have H := VanishTo.sum Finset.univ (fun i _ =>
    VanishTo.sum Finset.univ (fun j _ => hp i j))
  simpa [waveQuadratic, Finset.sum_sub_distrib, Finset.sum_add_distrib, two_mul] using H

end FiniteJets

section FiniteEikonal
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem eikonal_initial_order (G : σ → σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hdG : ∀ i j k, constantCoeff (pderiv k (G i j)) = 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i)
    (hnull : ∑ i, z i * z i = -1)
    (hcompat : ∀ k, ∑ i, z i * constantCoeff (pderiv k (pderiv i S)) = 0) :
    VanishTo (eikonalResidual G S) 2 := by
  apply VanishTo.of_constant_and_linear
  · simp [eikonalResidual, waveQuadratic, hG, hS, hnull]
  · intro k
    simp [eikonalResidual, waveQuadratic, hG, hdG, hS,
      Finset.sum_add_distrib, mul_comm, hcompat]

theorem eikonal_linearization (G : σ → σ → MvPolynomial σ ℂ)
    (S F : MvPolynomial σ ℂ) (z : σ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (hF : VanishTo F (N + 1)) :
    VanishTo (eikonalResidual G (S + F) - eikonalResidual G S -
      2 * waveDirectionalDerivative z F) (N + 1) := by
  have h := waveQuadratic_linearization G (fun i => pderiv i S)
    (fun i => pderiv i F) z N hN hG hS (hF.pderiv)
  simpa only [eikonalResidual, map_add, add_sub_add_left_eq_sub,
    waveDirectionalDerivative_apply, C_mul'] using h

end FiniteEikonal

section FiniteTransport
open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem waveTransport_add (A : σ → MvPolynomial σ ℂ) (B V W : MvPolynomial σ ℂ) :
    waveTransport A B (V + W) = waveTransport A B V + waveTransport A B W := by
  simp only [waveTransport, map_add, mul_add, Finset.sum_add_distrib]
  ring

theorem transport_linearization (A : σ → MvPolynomial σ ℂ) (B : MvPolynomial σ ℂ)
    (z : σ → ℂ) (N : ℕ) (hA : ∀ i, constantCoeff (A i) = 2 * z i)
    (F : MvPolynomial σ ℂ) (hF : VanishTo F (N + 1)) :
    VanishTo (waveTransport A B F - 2 * waveDirectionalDerivative z F) (N + 1) := by
  have hd (i : σ) : VanishTo ((A i - C (2 * z i)) * pderiv i F) (N + 1) := by
    have ha : VanishTo (A i - C (2 * z i)) 1 := by
      apply VanishTo.of_constantCoeff_eq_zero
      simp [hA]
    simpa only [Nat.add_comm 1] using ha.mul (hF.pderiv i)
  have H := (VanishTo.sum Finset.univ (fun i _ => hd i)).add (hF.mul_left B)
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  simp only [waveTransport, waveDirectionalDerivative_apply, sub_mul, Finset.sum_sub_distrib,
    ← C_mul', map_mul, map_ofNat, Finset.mul_sum]
  ring_nf

end FiniteTransport
section QuadraticSeed
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem wavePhaseSeed_eikonal (G : σ → σ → MvPolynomial σ ℂ)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hdG : ∀ i j k, constantCoeff (pderiv k (G i j)) = 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) :
    VanishTo (eikonalResidual G (wavePhaseSeed c z Q)) 2 := by
  apply eikonal_initial_order G _ z hG hdG (wavePhaseSeed_gradient c z Q) hnull
  intro k
  simpa only [wavePhaseSeed_hessian c z Q hQ] using hQz k

end QuadraticSeed

open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem wavePrimitive_homogeneous (z : σ → ℂ) (d : ℕ)
    (p : MvPolynomial σ ℂ) (hp : p.IsHomogeneous d) :
    (wavePrimitive z d p).IsHomogeneous (d + 1) := by
  simpa only [wavePrimitive, zero_add, add_zero] using
    wavePrimitiveTerm_homogeneous z (waveLinearCoordinate z)
      (waveLinearCoordinate_homogeneous z) d 0 p hp

theorem wavePrimitive_derivative (z : σ → ℂ) (hz : z ≠ 0) (d : ℕ)
    (p : MvPolynomial σ ℂ) (hp : p.IsHomogeneous d) :
    waveDirectionalDerivative z (wavePrimitive z d p) = p := by
  simpa only [wavePrimitive, pow_zero, one_mul] using
    wavePrimitiveTerm_derivative z (waveLinearCoordinate z)
      (waveLinearCoordinate_derivative z hz) d 0 p hp

theorem eikonalCorrection_homogeneous (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (N : ℕ) (S : MvPolynomial σ ℂ) :
    (eikonalCorrection G z N S).IsHomogeneous (N + 1) := by
  apply wavePrimitive_homogeneous
  simpa only [C_mul'] using
    (homogeneousComponent_isHomogeneous N (eikonalResidual G S)).C_mul (-((2 : ℂ)⁻¹))

variable [DecidableEq σ]

theorem eikonalCorrection_raises (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : z ≠ 0) (N : ℕ) (hN : 1 ≤ N) (S : MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i)
    (hE : VanishTo (eikonalResidual G S) N) :
    VanishTo (eikonalResidual G (S + eikonalCorrection G z N S)) (N + 1) := by
  have hp : (-((2 : ℂ)⁻¹) • homogeneousComponent N (eikonalResidual G S)).IsHomogeneous N := by
    simpa only [C_mul'] using
      (homogeneousComponent_isHomogeneous N (eikonalResidual G S)).C_mul (-((2 : ℂ)⁻¹))
  have hd : 2 * waveDirectionalDerivative z (eikonalCorrection G z N S) =
      -homogeneousComponent N (eikonalResidual G S) := by
    rw [eikonalCorrection, wavePrimitive_derivative z hz N _ hp, two_mul, ← add_smul]
    norm_num
  have hl := eikonal_linearization G S (eikonalCorrection G z N S) z N hN hG hS
    (VanishTo.of_homogeneous (eikonalCorrection_homogeneous G z N S))
  have H := hl.add hE.remove_component
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rw [hd]
  ring

theorem eikonalIter_spec (G : σ → σ → MvPolynomial σ ℂ)
    (z : σ → ℂ) (hz : z ≠ 0) (S₀ : MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS₀ : ∀ i, constantCoeff (pderiv i S₀) = z i)
    (hE₀ : VanishTo (eikonalResidual G S₀) 2) (k : ℕ) :
    VanishTo (eikonalIter G z S₀ k - S₀) 3 ∧
    VanishTo (eikonalResidual G (eikonalIter G z S₀ k)) (k + 2) ∧
    (eikonalIter G z S₀ k).totalDegree ≤ max S₀.totalDegree (k + 2) := by
  induction k with
  | zero =>
    exact ⟨by simpa [eikonalIter] using VanishTo.zero (σ := σ) (R := ℂ) 3,
      hE₀, le_max_left _ _⟩
  | succ k ih =>
    obtain ⟨hdiff, hE, hdeg⟩ := ih
    have hS (i : σ) : constantCoeff (pderiv i (eikonalIter G z S₀ k)) = z i := by
      have hd := (hdiff.pderiv i).constantCoeff_eq_zero (by decide)
      rw [map_sub, map_sub] at hd
      exact (sub_eq_zero.mp hd).trans (hS₀ i)
    have hF := eikonalCorrection_homogeneous G z (k + 2) (eikonalIter G z S₀ k)
    refine ⟨?_, ?_, ?_⟩
    · have hv : VanishTo (eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k)) 3 :=
        (VanishTo.of_homogeneous hF).mono (by omega)
      convert hdiff.add hv using 1
      all_goals try with_reducible_and_instances rfl
      simp only [eikonalIter]
      ring
    · simpa only [eikonalIter, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 2] using
        eikonalCorrection_raises G z hz (k + 2) (by omega) _ hG hS hE
    · have hfdeg := hF.totalDegree_le
      have hd := totalDegree_add (eikonalIter G z S₀ k)
        (eikonalCorrection G z (k + 2) (eikonalIter G z S₀ k))
      simp only [eikonalIter]
      omega



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section ActualEikonal
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem realTaylorPolynomial_constant {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} (hN : 0 < N) :
    constantCoeff (realTaylorPolynomial f N) = f 0 := by
  have h := realTaylorPolynomial_jet hf N 0 hN
  have hh := congrArg (fun B => B (fun i : Fin 0 => nomatch i)) h
  simpa only [iteratedFDeriv_zero_apply, realPolyEval_at_zero] using hh

theorem realTaylorPolynomial_linear {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} (hN : 1 < N) (i : σ) :
    constantCoeff (pderiv i (realTaylorPolynomial f N)) =
      fderiv ℝ f 0 (Pi.single i 1) := by
  classical
  have h := realTaylorPolynomial_jet hf N 1 hN
  have hh := congrArg (fun B => B (fun _ => Pi.single i 1)) h
  simpa [iteratedFDeriv_one_apply, fderiv_realPolyEval, Pi.single_apply, apply_ite] using hh

theorem realTaylorPolynomial_remainder {f : (σ → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    SmoothJetZero (f - realPolyEval (realTaylorPolynomial f N)) N := by
  intro k hk
  have hle : (k : ℕ∞ω) ≤ ∞ := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
  rw [iteratedFDeriv_sub_apply (hf.of_le hle).contDiffAt
    ((contDiff_realPolyEval _).of_le hle).contDiffAt,
    realTaylorPolynomial_jet hf N k hk, sub_self]

omit [DecidableEq σ] in
theorem VanishTo.realPolyEval {p : MvPolynomial σ ℂ} {N : ℕ} (h : VanishTo p N) :
    SmoothJetZero (YauCounterexamples.realPolyEval p) N := by
  intro k hk
  apply realPolyEval_jet_zero_of_coeff
  exact fun d hd => h d (by omega)

omit [DecidableEq σ] in
theorem contDiff_smoothEikonalResidual (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (smoothEikonalResidual g S) := by
  apply contDiff_const.add
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((hg i j).mul (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)

theorem smoothEikonalResidual_jet (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : MvPolynomial σ ℂ) (N : ℕ)
    (hE : VanishTo (eikonalResidual (fun i j => realTaylorPolynomial (g i j) N) S) N) :
    SmoothJetZero (smoothEikonalResidual g S) N := by
  let G := fun i j => realTaylorPolynomial (g i j) N
  let D : σ → σ → (σ → ℝ) → ℂ := fun i j x =>
    (g i j x - realPolyEval (G i j) x) *
      realPolyEval (pderiv i S) x * realPolyEval (pderiv j S) x
  have hd (i j : σ) : ContDiff ℝ ∞ (D i j) :=
    (((hg i j).sub (contDiff_realPolyEval _)).mul
      (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hdj (i j : σ) : SmoothJetZero (D i j) N :=
    ((realTaylorPolynomial_remainder (hg i j) N).mul_right
      ((hg i j).sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)).mul_right
        (((hg i j).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)) _
        (contDiff_realPolyEval _)
  have hc (i : σ) : ContDiff ℝ ∞ (∑ j, D i j) := by
    simpa only [Finset.sum_fn] using
      (ContDiff.sum (s := Finset.univ) (fun j _ => hd i j))
  have hcs : ContDiff ℝ ∞ (∑ i, ∑ j, D i j) := by
    simpa only [Finset.sum_fn] using
      (ContDiff.sum (s := Finset.univ) (fun i _ => hc i))
  have hds : SmoothJetZero (∑ i, ∑ j, D i j) N :=
    SmoothJetZero.sum Finset.univ _ (fun i _ => hc i)
      (fun i _ => SmoothJetZero.sum Finset.univ _ (fun j _ => hd i j) (fun j _ => hdj i j))
  have heq : smoothEikonalResidual g S =
      realPolyEval (eikonalResidual G S) + ∑ i, ∑ j, D i j := by
    funext x
    simp only [smoothEikonalResidual, eikonalResidual, waveQuadratic, Pi.add_apply,
      Finset.sum_apply, realPolyEval, map_add, map_one, map_sum, map_mul, D]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact hE.realPolyEval.add (contDiff_realPolyEval _)
    hcs hds

end ActualEikonal



end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_HessianJet
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section SecondJetBridge
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianFromJet_iterated (f : E → F) (x : E) :
    hessianFromJet (iteratedFDeriv ℝ 2 f x) = fderiv ℝ (fderiv ℝ f) x := by
  ext v w
  change (iteratedFDeriv ℝ 2 f x) (Fin.cons v (fun _ => w)) = _
  simpa using iteratedFDeriv_two_apply (𝕜 := ℝ) f x (Fin.cons v (fun _ => w))

lemma continuous_hessian_of_iterated {X : Type*} [TopologicalSpace X]
    (f : X → E → F)
    (hf : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (f q.1) q.2)) :
    Continuous (fun q : X × E => fderiv ℝ (fderiv ℝ (f q.1)) q.2) := by
  simpa only [Function.comp_def, hessianFromJet_iterated] using hessianFromJet.continuous.comp hf

end SecondJetBridge



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_TransportCorrection
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
namespace YauCounterexamples
variable {σ : Type*} [Fintype σ]

theorem transportCorrection_homogeneous (A : σ → MvPolynomial σ ℂ)
    (B V F : MvPolynomial σ ℂ) (z : σ → ℂ) (N : ℕ) :
    (transportCorrection A B V F z N).IsHomogeneous (N+1) := by
  apply wavePrimitive_homogeneous
  simpa only [C_mul'] using
    (homogeneousComponent_isHomogeneous N (waveTransport A B V + F)).C_mul (-((2:ℂ)⁻¹))

theorem transportCorrection_raises (A : σ → MvPolynomial σ ℂ)
    (B V F : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0) (N : ℕ)
    (hA : ∀ i, constantCoeff (A i) = 2*z i)
    (hR : VanishTo (waveTransport A B V + F) N) :
    VanishTo (waveTransport A B (V + transportCorrection A B V F z N) + F) (N+1) := by
  have hp : (-((2:ℂ)⁻¹) • homogeneousComponent N (waveTransport A B V + F)).IsHomogeneous N := by
    simpa only [C_mul'] using
      (homogeneousComponent_isHomogeneous N (waveTransport A B V + F)).C_mul (-((2:ℂ)⁻¹))
  have hd : 2 * waveDirectionalDerivative z (transportCorrection A B V F z N) =
      -homogeneousComponent N (waveTransport A B V + F) := by
    rw [transportCorrection,wavePrimitive_derivative z hz N _ hp,two_mul,← add_smul]
    norm_num
    abel
  have hl := transport_linearization A B z N hA _
    (VanishTo.of_homogeneous (transportCorrection_homogeneous A B V F z N))
  have H := hl.add hR.remove_component
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  rw [hd,waveTransport_add]
  ring

theorem transportIter_spec (A : σ → MvPolynomial σ ℂ)
    (B F : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hA : ∀ i, constantCoeff (A i) = 2*z i) (c : ℂ) (N : ℕ) :
    constantCoeff (transportIter A B F z c N) = c ∧
      VanishTo (waveTransport A B (transportIter A B F z c N) + F) N ∧
      (transportIter A B F z c N).totalDegree ≤ N := by
  induction N with
  | zero => exact ⟨by simp [transportIter],VanishTo.order_zero _,by simp [transportIter]⟩
  | succ N ih =>
    have hc := (VanishTo.of_homogeneous
      (transportCorrection_homogeneous A B (transportIter A B F z c N) F z N)).constantCoeff_eq_zero (by omega)
    refine ⟨?_,transportCorrection_raises A B _ F z hz N hA ih.2.1,?_⟩
    · simp [transportIter,ih.1,hc]
    · exact (totalDegree_add _ _).trans (max_le (by omega)
        (transportCorrection_homogeneous A B (transportIter A B F z c N) F z N).totalDegree_le)

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_PolynomialFiniteWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
lemma contDiff_smoothPolynomialLaplacian (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (P : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (smoothPolynomialLaplacian g b P) := by
  exact (ContDiff.sum (fun i _ => ContDiff.sum
    (fun j _ => (hg i j).mul (contDiff_realPolyEval _)))).add
      (ContDiff.sum (fun i _ => (hb i).mul (contDiff_realPolyEval _)))

lemma waveDeriv_realPolyEval_single (i : σ) (P : MvPolynomial σ ℂ) :
    waveDeriv (Pi.single i 1) (realPolyEval P) = realPolyEval (pderiv i P) := by
  funext x
  simp [waveDeriv, fderiv_realPolyEval, Pi.single_apply, apply_ite]

lemma smoothPolynomialLaplacian_eq_operator (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (P : MvPolynomial σ ℂ) :
    smoothPolynomialLaplacian g b P =
      waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval P) := by
  funext x
  simp only [waveCoordinateOperator, waveDeriv_realPolyEval_single,
    smoothPolynomialLaplacian]

omit [DecidableEq σ] in
lemma contDiff_smoothPhaseTransportVector (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (S : MvPolynomial σ ℂ) (i : σ) :
    ContDiff ℝ ∞ (smoothPhaseTransportVector g S i) :=
  ContDiff.sum (fun j _ => ((hg i j).add (hg j i)).mul (contDiff_realPolyEval _))

omit [DecidableEq σ] in
lemma contDiff_smoothPhaseTransportScalar (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (S : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (smoothPhaseTransportScalar g b S) :=
  (contDiff_smoothPolynomialLaplacian g b hg hb S).add contDiff_const

omit [DecidableEq σ] in
lemma sum_transport_product (G : σ → σ → ℂ) (s v : σ → ℂ) :
    (∑ i, (∑ j, (G i j + G j i) * s j) * v i) =
      (∑ i, ∑ j, G i j * v i * s j) + (∑ i, ∑ j, G i j * s i * v j) := by
  simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Finset.sum_comm]

lemma smoothWaveTransport_eq_finite (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (S V : MvPolynomial σ ℂ) :
    smoothWaveTransport (smoothPhaseTransportVector g S)
      (smoothPhaseTransportScalar g b S) V =
    finiteWaveTransport (fun i => Pi.single i 1) g b (realPolyEval S) (realPolyEval V) := by
  funext x
  simp only [smoothWaveTransport, smoothPhaseTransportVector, smoothPhaseTransportScalar,
    finiteWaveTransport, waveGradientPair, waveDeriv_realPolyEval_single,
    ← smoothPolynomialLaplacian_eq_operator]
  rw [sum_transport_product]

lemma smoothPhasePolynomial_spec (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) (L : ℕ) (hL : 2 ≤ L) :
    let S := smoothPhasePolynomial g c z Q L
    VanishTo (S - wavePhaseSeed c z Q) 3 ∧
      (∀ i, constantCoeff (pderiv i S) = z i) ∧
      SmoothJetZero (smoothEikonalResidual g S) L ∧
      S.totalDegree ≤ max (wavePhaseSeed c z Q).totalDegree L := by
  let G := fun i j => realTaylorPolynomial (g i j) L
  have hG (i j : σ) : constantCoeff (G i j) = if i = j then 1 else 0 :=
    (realTaylorPolynomial_constant (hg i j) (by omega)).trans (hg0 i j)
  have hdG (i j l : σ) : constantCoeff (pderiv l (G i j)) = 0 := by
    rw [realTaylorPolynomial_linear (hg i j) (by omega), hdg0 i j]
    rfl
  obtain ⟨hS, hE, hdegree⟩ := eikonalIter_spec G z hz (wavePhaseSeed c z Q) hG
    (wavePhaseSeed_gradient c z Q)
    (wavePhaseSeed_eikonal G c z Q hG hdG hQ hnull hQz) (L - 2)
  have horder : L - 2 + 2 = L := by omega
  rw [horder] at hE hdegree
  refine ⟨hS, ?_, smoothEikonalResidual_jet g hg _ L hE, hdegree⟩
  intro i
  have hd := (hS.pderiv i).constantCoeff_eq_zero (by decide)
  simp only [map_sub, wavePhaseSeed_gradient] at hd
  exact sub_eq_zero.mp hd



end

section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [TopologicalSpace X]

lemma formalPhaseTransportVector_constant (G : σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (i : σ) :
    constantCoeff (formalPhaseTransportVector G S i) = 2 * z i := by
  simp only [formalPhaseTransportVector, map_sum, map_mul, map_add, hG, hS]
  simp [eq_comm, ite_add_ite, ite_mul, two_mul]
  ring

omit [DecidableEq σ] in
lemma smoothPolynomialLaplacian_approx (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (G : σ → σ → MvPolynomial σ ℂ) (B : σ → MvPolynomial σ ℂ) (N : ℕ)
    (hG : ∀ i j, SmoothJetZero (g i j - realPolyEval (G i j)) N)
    (hB : ∀ i, SmoothJetZero (b i - realPolyEval (B i)) N) (P : MvPolynomial σ ℂ) :
    SmoothJetZero (smoothPolynomialLaplacian g b P -
      realPolyEval (formalPolynomialLaplacian G B P)) N := by
  let D := fun i j x => (g i j x - realPolyEval (G i j) x) *
    realPolyEval (pderiv i (pderiv j P)) x
  let F := fun i x => (b i x - realPolyEval (B i) x) * realPolyEval (pderiv i P) x
  have hd (i j : σ) : ContDiff ℝ ∞ (D i j) :=
    ((hg i j).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hf (i : σ) : ContDiff ℝ ∞ (F i) :=
    ((hb i).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hds (i : σ) : ContDiff ℝ ∞ (∑ j, D i j) := by
    simpa only [Finset.sum_fn] using ContDiff.sum (s := Finset.univ) (fun j _ => hd i j)
  have hdss : ContDiff ℝ ∞ (∑ i, ∑ j, D i j) := by
    simpa only [Finset.sum_fn] using ContDiff.sum (s := Finset.univ) (fun i _ => hds i)
  have hfs : ContDiff ℝ ∞ (∑ i, F i) := by
    simpa only [Finset.sum_fn] using ContDiff.sum (s := Finset.univ) (fun i _ => hf i)
  have heq : smoothPolynomialLaplacian g b P - realPolyEval (formalPolynomialLaplacian G B P) =
      (∑ i, ∑ j, D i j) + ∑ i, F i := by
    funext x
    simp only [smoothPolynomialLaplacian, formalPolynomialLaplacian, Pi.sub_apply,
      Pi.add_apply, Finset.sum_apply, realPolyEval, map_add, map_sum, map_mul, D, F,
      sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact (SmoothJetZero.sum Finset.univ _ (fun i _ => hds i)
    (fun i _ => SmoothJetZero.sum Finset.univ _ (fun j _ => hd i j)
      (fun j _ => (hG i j).mul_right ((hg i j).sub (contDiff_realPolyEval _)) _
        (contDiff_realPolyEval _)))).add hdss hfs
    (SmoothJetZero.sum Finset.univ _ (fun i _ => hf i)
      (fun i _ => (hB i).mul_right ((hb i).sub (contDiff_realPolyEval _)) _
        (contDiff_realPolyEval _)))

omit [DecidableEq σ] in
lemma smoothPhaseTransportVector_approx (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (G : σ → σ → MvPolynomial σ ℂ) (N : ℕ)
    (hG : ∀ i j, SmoothJetZero (g i j - realPolyEval (G i j)) N)
    (S : MvPolynomial σ ℂ) (i : σ) :
    SmoothJetZero (smoothPhaseTransportVector g S i -
      realPolyEval (formalPhaseTransportVector G S i)) N := by
  let D := fun j x => ((g i j x - realPolyEval (G i j) x) +
    (g j i x - realPolyEval (G j i) x)) * realPolyEval (pderiv j S) x
  have hd (j : σ) : ContDiff ℝ ∞ (D j) :=
    (((hg i j).sub (contDiff_realPolyEval _)).add
      ((hg j i).sub (contDiff_realPolyEval _))).mul (contDiff_realPolyEval _)
  have heq : smoothPhaseTransportVector g S i - realPolyEval (formalPhaseTransportVector G S i) =
      ∑ j, D j := by
    funext x
    simp only [smoothPhaseTransportVector, formalPhaseTransportVector, Pi.sub_apply,
      Finset.sum_apply, realPolyEval, map_sum, map_mul, map_add, D]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  exact SmoothJetZero.sum Finset.univ _ (fun j _ => hd j) (fun j _ =>
    ((hG i j).add ((hg i j).sub (contDiff_realPolyEval _))
      ((hg j i).sub (contDiff_realPolyEval _)) (hG j i)).mul_right
        (((hg i j).sub (contDiff_realPolyEval _)).add
          ((hg j i).sub (contDiff_realPolyEval _))) _ (contDiff_realPolyEval _))

omit [DecidableEq σ] in
lemma smoothWaveTransport_jet_approx (a : σ → (σ → ℝ) → ℂ)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (b f : (σ → ℝ) → ℂ)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f)
    (A : σ → MvPolynomial σ ℂ) (B F V : MvPolynomial σ ℂ) (N : ℕ)
    (hA : ∀ i, SmoothJetZero (a i - realPolyEval (A i)) N)
    (hB : SmoothJetZero (b - realPolyEval B) N)
    (hF : SmoothJetZero (f - realPolyEval F) N)
    (hR : VanishTo (waveTransport A B V + F) N) :
    SmoothJetZero (smoothWaveTransport a b V + f) N := by
  let D := fun i x => (a i x - realPolyEval (A i) x) * realPolyEval (pderiv i V) x
  let D₀ := fun x => (b x - realPolyEval B x) * realPolyEval V x
  have hD (i : σ) : ContDiff ℝ ∞ (D i) :=
    ((ha i).sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hD₀ : ContDiff ℝ ∞ D₀ :=
    (hb.sub (contDiff_realPolyEval _)).mul (contDiff_realPolyEval _)
  have hDs : ContDiff ℝ ∞ (∑ i, D i) := by
    simpa only [Finset.sum_fn] using (ContDiff.sum (s := Finset.univ) (fun i _ => hD i))
  have hj (i : σ) : SmoothJetZero (D i) N :=
    (hA i).mul_right ((ha i).sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)
  have hj₀ : SmoothJetZero D₀ N := hB.mul_right
      (hb.sub (contDiff_realPolyEval _)) _ (contDiff_realPolyEval _)
  have hjs : SmoothJetZero (∑ i, D i) N :=
    SmoothJetZero.sum Finset.univ _ (fun i _ => hD i) (fun i _ => hj i)
  have heq : smoothWaveTransport a b V + f =
      realPolyEval (waveTransport A B V + F) +
        ((∑ i, D i) + D₀ + (f - realPolyEval F)) := by
    funext x
    simp only [smoothWaveTransport, waveTransport, Pi.add_apply, Pi.sub_apply,
      Finset.sum_apply, realPolyEval, map_add, map_sum, map_mul, D, D₀]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  exact hR.realPolyEval.add (contDiff_realPolyEval _)
    ((hDs.add hD₀).add (hf.sub (contDiff_realPolyEval _)))
    ((hjs.add hDs hD₀ hj₀).add (hDs.add hD₀) (hf.sub (contDiff_realPolyEval _)) hF)

lemma symbolWaveAmplitudes_spec (G : σ → σ → MvPolynomial σ ℂ)
    (B : σ → MvPolynomial σ ℂ) (S : MvPolynomial σ ℂ) (z : σ → ℂ)
    (hz : z ≠ 0) (hG : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ) :
    let V := symbolWaveAmplitudes G B S z K J
    (∀ j, constantCoeff (V j) = if j = 0 then 1 else 0) ∧
    (∀ j, (V j).totalDegree ≤ K+J-j) ∧
    VanishTo (waveTransport (formalPhaseTransportVector G S)
      (formalPhaseTransportScalar G B S) (V 0)) (K+J) ∧
    (∀ j, VanishTo (waveTransport (formalPhaseTransportVector G S)
      (formalPhaseTransportScalar G B S) (V (j+1)) + formalPolynomialLaplacian G B (V j))
      (K+J-(j+1))) := by
  dsimp only
  have hA := formalPhaseTransportVector_constant G hG S z hS
  have h0 := transportIter_spec (formalPhaseTransportVector G S)
    (formalPhaseTransportScalar G B S) 0 z hz hA 1 (K+J)
  have hj (j : ℕ) := transportIter_spec (formalPhaseTransportVector G S)
    (formalPhaseTransportScalar G B S)
    (formalPolynomialLaplacian G B (symbolWaveAmplitudes G B S z K J j)) z hz hA 0 (K+J-(j+1))
  exact ⟨fun j => by cases j with
    | zero => exact h0.1
    | succ j => exact (hj j).1,
    fun j => by cases j with
    | zero => exact h0.2.2
    | succ j => exact (hj j).2.2,
    by simpa only [add_zero, symbolWaveAmplitudes] using h0.2.1, fun j => (hj j).2.1⟩

lemma symbolWaveAmplitudes_genuine (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (G : σ → σ → MvPolynomial σ ℂ) (B : σ → MvPolynomial σ ℂ)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hG0 : ∀ i j, constantCoeff (G i j) = if i = j then 1 else 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ)
    (hG : ∀ i j, SmoothJetZero (g i j - realPolyEval (G i j)) (K+J))
    (hB : ∀ i, SmoothJetZero (b i - realPolyEval (B i)) (K+J)) :
    let V := symbolWaveAmplitudes G B S z K J
    SmoothJetZero (finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V 0))) (K+J) ∧
    (∀ j, SmoothJetZero (fun x => finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V (j+1))) x +
        waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval (V j)) x)
      (K+J-(j+1))) := by
  let V := symbolWaveAmplitudes G B S z K J
  have hspec := symbolWaveAmplitudes_spec G B S z hz hG0 hS K J
  have hA := smoothPhaseTransportVector_approx g hg G (K+J) hG S
  have hT : SmoothJetZero (smoothPhaseTransportScalar g b S -
      realPolyEval (formalPhaseTransportScalar G B S)) (K+J) := by
    convert smoothPolynomialLaplacian_approx g b hg hb G B (K+J) hG hB S using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp [smoothPhaseTransportScalar, formalPhaseTransportScalar, realPolyEval]
  constructor
  · rw [← smoothWaveTransport_eq_finite]
    have h := smoothWaveTransport_jet_approx (smoothPhaseTransportVector g S)
      (contDiff_smoothPhaseTransportVector g hg S) (smoothPhaseTransportScalar g b S) 0
      (contDiff_smoothPhaseTransportScalar g b hg hb S) contDiff_const
      (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S) 0 (V 0) (K+J)
      hA hT (by
        convert SmoothJetZero.zero (E := σ → ℝ) (F := ℂ) (K+J) using 1
        all_goals try with_reducible_and_instances rfl
        ext x; simp [realPolyEval])
      (by simpa only [add_zero] using hspec.2.2.1)
    simpa only [add_zero] using h
  · intro j
    rw [← smoothWaveTransport_eq_finite, ← smoothPolynomialLaplacian_eq_operator]
    exact smoothWaveTransport_jet_approx (smoothPhaseTransportVector g S)
      (contDiff_smoothPhaseTransportVector g hg S) (smoothPhaseTransportScalar g b S)
      (smoothPolynomialLaplacian g b (V j))
      (contDiff_smoothPhaseTransportScalar g b hg hb S)
      (contDiff_smoothPolynomialLaplacian g b hg hb _)
      (formalPhaseTransportVector G S) (formalPhaseTransportScalar G B S)
      (formalPolynomialLaplacian G B (V j)) (V (j+1)) (K+J-(j+1))
      (fun i => (hA i).mono (Nat.sub_le _ _)) (hT.mono (Nat.sub_le _ _))
      ((smoothPolynomialLaplacian_approx g b hg hb G B (K+J) hG hB _).mono (Nat.sub_le _ _))
      (hspec.2.2.2 j)

lemma uniformSmoothWaveAmplitudes_genuine (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (S : MvPolynomial σ ℂ) (z : σ → ℂ) (hz : z ≠ 0)
    (hS : ∀ i, constantCoeff (pderiv i S) = z i) (K J : ℕ) (hKJ : 0 < K+J) :
    let V := uniformSmoothWaveAmplitudes g b S z K J
    (∀ j, constantCoeff (V j) = if j = 0 then 1 else 0) ∧
    (∀ j, (V j).totalDegree ≤ K+J-j) ∧
    SmoothJetZero (finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V 0))) (K+J) ∧
    (∀ j, SmoothJetZero (fun x => finiteWaveTransport (fun i => Pi.single i 1) g b
      (realPolyEval S) (realPolyEval (V (j+1))) x +
        waveCoordinateOperator (fun i => Pi.single i 1) g b (realPolyEval (V j)) x)
      (K+J-(j+1))) := by
  let G := fun i j => realTaylorPolynomial (g i j) (K+J)
  let B := fun i => realTaylorPolynomial (b i) (K+J)
  have hG0 (i j : σ) : constantCoeff (G i j) = if i = j then 1 else 0 :=
    (realTaylorPolynomial_constant (hg i j) hKJ).trans (hg0 i j)
  have hs := symbolWaveAmplitudes_spec G B S z hz hG0 hS K J
  have hgenuine := symbolWaveAmplitudes_genuine g b hg hb G B S z hz hG0 hS K J
    (fun i j => realTaylorPolynomial_remainder (hg i j) (K+J))
    (fun i => realTaylorPolynomial_remainder (hb i) (K+J))
  exact ⟨hs.1, hs.2.1, hgenuine⟩


end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

lemma generated_wave_remainders_vanish (g : σ → σ → (σ → ℝ) → ℂ)
    (b : σ → (σ → ℝ) → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (s : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i*z i = -1)
    (hQz : ∀ k, ∑ i, z i*Q k i = 0) (K J : ℕ) (hK : 1 ≤ K) :
    let S := smoothPhasePolynomial g s z Q (K+J+1)
    let V := uniformSmoothWaveAmplitudes g b S z K J
    (∀ j, SmoothJetZero (fun x => smoothEikonalResidual g S x * realPolyEval (V j) x) K) ∧
    (∀ j ≤ J, SmoothJetZero (polynomialWaveRemainder g b S V j) K) := by
  dsimp only
  let S := smoothPhasePolynomial g s z Q (K+J+1)
  let V := uniformSmoothWaveAmplitudes g b S z K J
  have hs := smoothPhasePolynomial_spec g hg hg0 hdg0 s z Q hz hQ hnull hQz (K+J+1) (by omega)
  have hv := uniformSmoothWaveAmplitudes_genuine g b hg hb hg0 S z hz hs.2.1 K J (by omega)
  constructor
  · intro j
    exact (hs.2.2.1.mono (by omega)).mul_right (contDiff_smoothEikonalResidual g hg S)
      (realPolyEval (V j)) (contDiff_realPolyEval _)
  · intro j hj
    cases j with
    | zero =>
      rw [polynomialWaveRemainder, smoothWaveTransport_eq_finite]
      exact hv.2.2.1.mono (by omega)
    | succ j =>
      simp only [polynomialWaveRemainder, smoothWaveTransport_eq_finite,
        smoothPolynomialLaplacian_eq_operator]
      exact (hv.2.2.2 j).mono (by omega)

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_RealPhaseLinear
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι]

lemma phase_vector_ne_zero (z : ι → ℂ) (hz : ∑ i, z i*z i = -1) : z ≠ 0 := by
  intro he
  simp [he] at hz

lemma phase_matrix_annihilation (Q : Matrix ι ι ℂ) (z : ι → ℂ)
    (h : Q *ᵥ z = 0) (k : ι) : ∑ i, z i * Q k i = 0 := by
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using congrFun h k



end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Limits_ClosedPhaseMatrixValid
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {X : Type*} [TopologicalSpace X]

lemma isClosed_phaseMatrixValid (H : X → RealForm PhaseSpace) (z : X → Fin 3 → ℂ)
    (hH : Continuous (fun x => phaseFormMatrix (H x))) (hz : Continuous z)
    (κ C : ℝ) :
    IsClosed {p : X × ComplexPhaseMatrix | PhaseMatrixValid (H p.1) (z p.1) κ C p.2} := by
  have hs : IsClosed {p : X × ComplexPhaseMatrix | p.2ᵀ = p.2} :=
    isClosed_eq (by fun_prop) continuous_snd
  have ha : IsClosed {p : X × ComplexPhaseMatrix | p.2 *ᵥ z p.1 = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hb : IsClosed {p : X × ComplexPhaseMatrix | ‖p.2‖ ≤ C} :=
    isClosed_le continuous_snd.norm continuous_const
  have hg : IsClosed {p : X × ComplexPhaseMatrix | ∀ v,
      4*κ*squareSum v ≤ realQuadratic (phaseFormMatrix (H p.1)-p.2.map Complex.re) v} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold realQuadratic
    have hM : Continuous (fun p : X × ComplexPhaseMatrix => phaseFormMatrix (H p.1)) :=
      hH.comp continuous_fst
    fun_prop
  exact hs.inter (ha.inter (hb.inter hg))

theorem boundedPhaseSet_isCompact [CompactSpace X]
    (H : X → RealForm PhaseSpace) (hH : Continuous (fun x => phaseFormMatrix (H x)))
    (B κ C : ℝ) : IsCompact (boundedPhaseSet H B κ C) := by
  have hz : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) | ‖p.1.2‖ ≤ B} :=
    isClosed_le (continuous_snd.comp continuous_fst).norm continuous_const
  have hn : IsClosed {p : ((X × (Fin 3 → ℂ)) × ComplexPhaseMatrix) |
      ∑ i, p.1.2 i * p.1.2 i = -1} := isClosed_eq (by fun_prop) continuous_const
  have hv := isClosed_phaseMatrixValid (fun p : X × (Fin 3 → ℂ) => H p.1)
    (fun p => p.2) (hH.comp continuous_fst) continuous_snd κ C
  have hclosed : IsClosed (boundedPhaseSet H B κ C) := hz.inter (hn.inter hv)
  apply ((isCompact_univ.prod (isCompact_closedBall (0 : Fin 3 → ℂ) B)).prod
    (isCompact_closedBall (0 : ComplexPhaseMatrix) C)).of_isClosed_subset hclosed
  intro p hp
  exact ⟨⟨mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1⟩,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.2.2.2.1⟩

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_ActualHessianForm
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix Matrix.Norms.Elementwise
namespace YauCounterexamples

lemma continuous_actualHessianForm {X : Type*} [TopologicalSpace X]
    (φ : X → PhaseSpace → ℝ)
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2)) :
    Continuous (fun p => phaseFormMatrix (actualHessianForm (φ p))) := by
  have hH := (continuous_hessian_of_iterated φ hφ2).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => (0 : PhaseSpace))))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (hH.clm_apply continuous_const).clm_apply continuous_const

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Geometry_GaussianLinearDistortion
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
namespace YauCounterexamples

lemma gaussian_linear_distortion {κ A t : ℝ} (hκ : 0 < κ) :
    A*t-κ*t^2 ≤ t-κ/2*t^2 + (A-1)^2/(2*κ) := by
  have hc : 2*κ*((A-1)^2/(2*κ)) = (A-1)^2 := by field_simp
  nlinarith [sq_nonneg (κ*t-(A-1))]

lemma gaussian_phase_coordinate_shift {n κ A q s φ : ℝ}
    (hn : 0 < n) (hκ : 0 < κ)
    (hphase : n*(s-φ) ≤ A*Real.sqrt n*q-κ*n*q^2) :
    n*(s-(φ+(A-1)^2/(2*κ)/n)) ≤
      Real.sqrt n*q-(κ/2)*n*q^2 := by
  have hs := gaussian_linear_distortion (A := A) (t := Real.sqrt n*q) hκ
  rw [mul_pow,Real.sq_sqrt hn.le] at hs
  have he : n*((A-1)^2/(2*κ)/n) = (A-1)^2/(2*κ) := by field_simp
  nlinarith

lemma gaussian_phase_shift_exp {n κ A φ : ℝ} (hn : n ≠ 0) :
    Real.exp (n*(φ+(A-1)^2/(2*κ)/n)) =
      Real.exp ((A-1)^2/(2*κ))*Real.exp (n*φ) := by
  have he : n*(φ+(A-1)^2/(2*κ)/n) = (A-1)^2/(2*κ)+n*φ := by field_simp; ring
  rw [he,Real.exp_add]
end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_SmoothFiniteWaveSum
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
section UniformJetBounds
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma UniformJetBounds.mono {f : X → E → ℂ} {K K' : Set X} {B B' : Set E}
    (h : UniformJetBounds f K B) (hK : K' ⊆ K) (hB : B' ⊆ B) :
    UniformJetBounds f K' B' := by
  intro k
  obtain ⟨C,hC,h⟩ := h k
  exact ⟨C,hC,fun p hp x hx => h p (hK hp) x (hB hx)⟩

variable [TopologicalSpace X]
lemma uniformJetBounds_of_continuous_jets (f : X → E → ℂ)
    (hf : ∀ k, Continuous (fun q : X × E => iteratedFDeriv ℝ k (f q.1) q.2))
    {K : Set X} (hK : IsCompact K) {B : Set E} (hB : IsCompact B) :
    UniformJetBounds f K B := by
  intro k
  obtain ⟨C,hC⟩ := (hK.prod hB).exists_bound_of_continuousOn (hf k).continuousOn
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  exact fun p hp x hx => (hC (p,x) ⟨hp,hx⟩).trans (le_max_left _ _)
end UniformJetBounds

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff

end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CanonicalCutoffWave
attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {X : Type*}

theorem generated_cutoff_wave_residual_estimate [TopologicalSpace X]
    (g : X → σ → σ → (σ → ℝ) → ℂ) (b : X → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (hz₀ : ∀ p, z p ≠ 0) (Q : X → σ → σ → ℂ)
    (hQ : ∀ i j, Continuous (fun p => Q p i j)) (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (ζ : (σ → ℝ) → ℂ) (hζ : ContDiff ℝ ∞ ζ) (hζ₀ : ζ =ᶠ[𝓝 0] fun _ => 1)
    (m D : ℕ) (r c : ℝ) (hr : r ≤ 1) (hc : 0 < c)
    {P : Set X} (hP : IsCompact P) :
    let K := 2*D+3*m+6
    let J := D+m+1
    let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
    let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
    ∃ C > 0, ∀ p ∈ P, ∀ n : ℝ, 1 ≤ n → ∀ x ∈ Metric.ball (0 : σ → ℝ) r,
      ∀ φ : ℝ, n*((realPolyEval (S p) x).re-φ) ≤ Real.sqrt n*‖x‖-c*n*‖x‖^2 →
      ∀ k ≤ m, ‖iteratedFDeriv ℝ k (fun y =>
        waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p) (smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n) y +
         (n : ℂ)*((n : ℂ)+2)*smoothFiniteWave (realPolyEval (S p)) (fun j x => ζ x * realPolyEval (V p j) x) J n y) x‖ ≤
        C*(n^(D+1))⁻¹*Real.exp (n*φ) := by
  dsimp only
  let K := 2*D+3*m+6
  let J := D+m+1
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) (K+J+1)
  let V := fun p => uniformSmoothWaveAmplitudes (g p) (b p) (S p) (z p) K J
  have hu := generated_wave_uniform_jets g b hg hb hg0 hdg0 hgc hbc s hs z hz hz₀ Q hQ
    hsym hnull hQz K J (by dsimp [K]; omega) hP (isCompact_closedBall (0 : σ → ℝ) r)
  have hgB (i j) := (uniformJetBounds_of_continuous_jets (fun p => g p i j) (hgc i j) hP
    (isCompact_closedBall (0 : σ → ℝ) r)).mono subset_rfl Metric.ball_subset_closedBall
  have hbB (i) := (uniformJetBounds_of_continuous_jets (fun p => b p i) (hbc i) hP
    (isCompact_closedBall (0 : σ → ℝ) r)).mono subset_rfl Metric.ball_subset_closedBall
  apply cutoff_polynomial_wave_residual_bound g b hg hb S V ζ hζ hζ₀ m D J le_rfl r c hr hc P
    hgB hbB (hu.1.mono subset_rfl Metric.ball_subset_closedBall)
    (fun j => (hu.2.2.2.2 j).mono subset_rfl Metric.ball_subset_closedBall)
  · intro p hp j
    exact (generated_wave_remainders_vanish (g p) (b p) (hg p) (hb p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hsym p) (hnull p) (hQz p) K J (by dsimp [K]; omega)).1 j
  · intro p hp j hj
    exact (generated_wave_remainders_vanish (g p) (b p) (hg p) (hb p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hsym p) (hnull p) (hQz p) K J (by dsimp [K]; omega)).2 j hj

end

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Matrix MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma norm_pi_le_euclidean (x : Fin 3 → ℝ) : ‖x‖ ≤ ‖(WithLp.toLp 2 x : PhaseSpace)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    (fun i => PiLp.norm_apply_le (WithLp.toLp 2 x : PhaseSpace) i)

theorem admissible_cutoff_wave_residual_oai {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C : ℝ) {κ : ℝ} (hκ : 0 < κ) (m D : ℕ) :
    ∃ r > 0, ∀ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ → (ζ =ᶠ[𝓝 0] fun _ => 1) →
      ∃ A > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
        PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
        ∀ n : ℝ, 1 ≤ n → ‖phaseRealVector z-gradient (φ p) 0‖ ≤ (Real.sqrt n)⁻¹ →
        ∀ x ∈ Metric.ball (0 : Fin 3 → ℝ) r, ∀ k ≤ m,
          ‖iteratedFDeriv ℝ k (fun y =>
            waveCoordinateOperator (fun i => Pi.single i 1) (g p) (b p)
              (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n) y +
            (n : ℂ)*((n : ℂ)+2)*canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n y) x‖ ≤
            A*(n^(D+1))⁻¹*Real.exp (n*φ p (WithLp.toLp 2 x)) := by
  let K := 2*D+3*m+6
  let J := D+m+1
  have hgj : ∀ i j k, k < K+J+1 → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0) := by
    intro i j k _
    exact (hgc i j k).comp (continuous_id.prodMk continuous_const)
  obtain ⟨R,hR,hga⟩ := all_admissible_generated_gaussian g hg hg0 hdg0 φ hφ hφ0 hφ2
    (K+J+1) (by dsimp [K,J]; omega) hgj B C hκ
  let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  let a : ℝ := max ‖T‖ 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let r := min 1 (R/a)
  have hr : 0 < r := lt_min zero_lt_one (div_pos hR ha)
  refine ⟨r,hr,?_⟩
  intro ζ hζ hζ0
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  have hW : IsCompact W := boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let partition : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hπ : Continuous partition := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hn (p : W) : ∑ i, z p i*z p i = -1 := p.property.2.1
  have hv (p : W) : PhaseMatrixValid (H (partition p)) (z p) κ C (Q p) := p.property.2.2
  have hgc' : ∀ i j k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (partition q.1) i j) q.2) := by
    intro i j k
    exact (hgc i j k).comp ((hπ.comp continuous_fst).prodMk continuous_snd)
  have hbc' : ∀ i k, Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (b (partition q.1) i) q.2) := by
    intro i k
    exact (hbc i k).comp ((hπ.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨A,hA,hres⟩ := generated_cutoff_wave_residual_estimate
    (fun p : W => g (partition p)) (fun p => b (partition p)) (fun p => hg (partition p)) (fun p => hb (partition p))
    (fun p => hg0 (partition p)) (fun p => hdg0 (partition p)) hgc' hbc'
    (fun p => (φ (partition p) 0 : ℂ)) (Complex.continuous_ofReal.comp (hφ0.comp hπ))
    z (fun i => (continuous_apply i).comp hz) (fun p => phase_vector_ne_zero _ (hn p))
    Q (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p i j => congrFun (congrFun (hv p).1 j) i) hn
    (fun p k => phase_matrix_annihilation _ _ (hv p).2.1 k)
    ζ hζ hζ0 m D r (κ/2) (min_le_left _ _) (half_pos hκ) isCompact_univ
  refine ⟨A*Real.exp ((a-1)^2/(2*κ)),mul_pos hA (Real.exp_pos _),?_⟩
  intro p z0 Q0 hz0 hn0 hQ0 n hn1 hlin x hx k hk
  let w : W := ⟨((p,z0),Q0),hz0,hn0,hQ0⟩
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn1
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hxnorm : ‖x‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  have hTx : ‖T x‖ ≤ a*‖x‖ := (T.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x))
  have hxR : (WithLp.toLp 2 x : PhaseSpace) ∈ Metric.ball 0 R := by
    change ‖T x-0‖ < R
    rw [sub_zero]
    apply lt_of_le_of_lt hTx
    apply (mul_lt_mul_of_pos_left (hxnorm.trans_le (min_le_right _ _)) ha).trans_le
    exact le_of_eq (mul_div_cancel₀ R ha.ne')
  have hp := hga p z0 Q0 hz0 hn0 hQ0 (WithLp.toLp 2 x) hxR
  have hbound : n*((realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z0 Q0 (K+J+1)) x).re-
      φ p (WithLp.toLp 2 x)) ≤ a*Real.sqrt n*‖x‖-κ*n*‖x‖^2 := by
    have hsq := Real.sq_sqrt hnpos.le
    have hnl : n*‖phaseRealVector z0-gradient (φ p) 0‖ ≤ Real.sqrt n := by
      calc
        _ ≤ n*(Real.sqrt n)⁻¹ := mul_le_mul_of_nonneg_left hlin hnpos.le
        _ = Real.sqrt n := by field_simp; nlinarith
    have hpl := mul_le_mul_of_nonneg_right hnl (norm_nonneg (T x))
    have hmax := mul_le_mul_of_nonneg_left hTx hspos.le
    have hnorm : ‖x‖ ≤ ‖T x‖ := norm_pi_le_euclidean x
    have hquad : ‖x‖^2 ≤ ‖T x‖^2 := by nlinarith [norm_nonneg x,norm_nonneg (T x)]
    have hm := mul_le_mul_of_nonneg_left hquad (mul_nonneg hκ.le hnpos.le)
    have hp' := mul_le_mul_of_nonneg_left hp hnpos.le
    change n*((realPolyEval _ x).re-φ p (WithLp.toLp 2 x)) ≤
      n*(‖phaseRealVector z0-gradient (φ p) 0‖*‖T x‖-κ*‖T x‖^2) at hp'
    nlinarith
  have hbnd := gaussian_phase_coordinate_shift hnpos hκ hbound
  have hh := hres w (mem_univ w) n hn1 x hx
    (φ p (WithLp.toLp 2 x)+(a-1)^2/(2*κ)/n) hbnd k hk
  change ‖iteratedFDeriv ℝ k (fun y =>
    waveCoordinateOperator _ (g p) (b p) (canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z0 Q0 ζ m D n) y +
    (n : ℂ)*((n : ℂ)+2)*canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z0 Q0 ζ m D n y) x‖ ≤ _ at hh
  rw [gaussian_phase_shift_exp hnpos.ne'] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring


end YauCounterexamples
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.YauCounterexamples.admissible_cutoff_wave_residual_oai.{u_1} := @OAI.YauCounterexamples.admissible_cutoff_wave_residual_oai.{u_1}
