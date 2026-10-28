-- Prove2me | solution 1 for OAI.YauCounterexamples.canonical_phase_triple_smallBall
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:01:57.020216+00:00
-- url     : https://prove2.me/submissions/80ec38bd-e075-494c-8393-ed595e8aeeab

import Mathlib
import Definitions.Def_OAIQ070A010
import Theorems.Thm_OAI_YauCounterexamples_generated_cutoff_waves_near_center
import Theorems.Thm_OAI_YauCounterexamples_physical_complex_wave_smallBall_uniform

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

section CoefficientContinuity
open MvPolynomial
variable {σ X : Type*} [TopologicalSpace X]

namespace CoeffContinuous

theorem const (p : MvPolynomial σ ℂ) : CoeffContinuous (fun _ : X => p) :=
  fun _ => continuous_const

theorem add {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x + G x) := by
  intro m
  convert (hF m).add (hG m) using 1; ext x; simp

theorem neg {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => -F x) := by
  intro m
  convert (hF m).neg using 1; ext x; simp

theorem sub {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x - G x) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

theorem smul {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    {c : X → ℂ} (hc : Continuous c) : CoeffContinuous (fun x => c x • F x) := by
  intro m
  convert hc.mul (hF m) using 1; ext x; simp

theorem mul {F G : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F)
    (hG : CoeffContinuous G) : CoeffContinuous (fun x => F x * G x) := by
  classical
  intro m
  simp only [coeff_mul]
  apply continuous_finsetSum
  intro t _
  exact (hF t.1).mul (hG t.2)

theorem pow {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) (n : ℕ) :
    CoeffContinuous (fun x => F x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using const (X := X) (1 : MvPolynomial σ ℂ)
  | succ n ih => simpa only [pow_succ] using ih.mul hF

theorem sum {ι : Type*} (s : Finset ι) (F : ι → X → MvPolynomial σ ℂ)
    (hF : ∀ i ∈ s, CoeffContinuous (F i)) :
    CoeffContinuous (fun x => ∑ i ∈ s, F i x) := by
  intro m
  simp only [coeff_sum]
  exact continuous_finsetSum s (fun i hi => hF i hi m)

theorem pderiv {F : X → MvPolynomial σ ℂ} (hF : CoeffContinuous F) (i : σ) :
    CoeffContinuous (fun x => pderiv i (F x)) := by
  intro m
  simpa only [coeff_pderiv] using (hF (m + Finsupp.single i 1)).mul_const (m i + 1)

theorem homogeneousComponent {F : X → MvPolynomial σ ℂ}
    (hF : CoeffContinuous F) (N : ℕ) :
    CoeffContinuous (fun x => homogeneousComponent N (F x)) := by
  intro m
  simp only [coeff_homogeneousComponent]
  split_ifs
  · exact hF m
  · exact continuous_const

end CoeffContinuous

variable [Fintype σ]

theorem waveDirectionalDerivative_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (F : X → MvPolynomial σ ℂ)
    (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => waveDirectionalDerivative (z x) (F x)) := by
  simp only [waveDirectionalDerivative_apply]
  exact CoeffContinuous.sum Finset.univ _ (fun i _ => (hF.pderiv i).smul (hz i))

theorem waveLinearCoordinate_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0) :
    CoeffContinuous (fun x => waveLinearCoordinate (z x)) := by
  have hd : Continuous (fun x => waveNormSq (z x)) := by
    exact continuous_finsetSum Finset.univ (fun i _ => Complex.continuous_normSq.comp (hz i))
  apply CoeffContinuous.sum
  intro i _
  apply (CoeffContinuous.const (MvPolynomial.X i)).smul
  exact (continuous_star.comp (hz i)).div (Complex.continuous_ofReal.comp hd)
    (fun x => by exact_mod_cast (ne_of_gt (waveNormSq_pos (z x) (hz₀ x))))

theorem wavePrimitiveTerm_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (ℓ : X → MvPolynomial σ ℂ)
    (hℓ : CoeffContinuous ℓ) (d j : ℕ) (F : X → MvPolynomial σ ℂ)
    (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => wavePrimitiveTerm (z x) (ℓ x) d j (F x)) := by
  induction d generalizing j F with
  | zero => exact ((hℓ.pow (j + 1)).mul hF).smul continuous_const
  | succ d ih =>
      exact (((hℓ.pow (j + 1)).mul hF).sub
        (ih (j + 1) _ (waveDirectionalDerivative_coeffContinuous z hz F hF))).smul continuous_const

theorem canonical_wavePrimitive_coeffContinuous (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0)
    (d : ℕ) (F : X → MvPolynomial σ ℂ) (hF : CoeffContinuous F) :
    CoeffContinuous (fun x => wavePrimitiveTerm (z x) (waveLinearCoordinate (z x)) d 0 (F x)) :=
  wavePrimitiveTerm_coeffContinuous z hz _ (waveLinearCoordinate_coeffContinuous z hz hz₀) d 0 F hF

end CoefficientContinuity

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

variable {X : Type*} [TopologicalSpace X]

omit [DecidableEq σ] in
theorem eikonalResidual_coeffContinuous (G : X → σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun x => G x i j)) (S : X → MvPolynomial σ ℂ)
    (hS : CoeffContinuous S) : CoeffContinuous (fun x => eikonalResidual (G x) (S x)) := by
  apply (CoeffContinuous.const 1).add
  apply CoeffContinuous.sum
  intro i _
  apply CoeffContinuous.sum
  intro j _
  exact ((hG i j).mul (hS.pderiv i)).mul (hS.pderiv j)

omit [DecidableEq σ] in
theorem eikonalIter_coeffContinuous (G : X → σ → σ → MvPolynomial σ ℂ)
    (hG : ∀ i j, CoeffContinuous (fun x => G x i j)) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun x => z x i)) (hz₀ : ∀ x, z x ≠ 0)
    (S₀ : X → MvPolynomial σ ℂ) (hS₀ : CoeffContinuous S₀) (k : ℕ) :
    CoeffContinuous (fun x => eikonalIter (G x) (z x) (S₀ x) k) := by
  induction k with
  | zero => exact hS₀
  | succ k ih =>
    apply ih.add
    apply canonical_wavePrimitive_coeffContinuous z hz hz₀
    exact ((eikonalResidual_coeffContinuous G hG _ ih).homogeneousComponent (k + 2)).smul
      continuous_const



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
variable {σ : Type*} [Fintype σ]

theorem bounded_degree_expansion (p : MvPolynomial σ ℂ) (N : ℕ)
    (hp : p.totalDegree ≤ N) :
    p = ∑ m ∈ boundedDegreeMonomials (σ:=σ) N, monomial m (p.coeff m) := by
  classical
  conv_lhs => rw [p.as_sum]
  apply Finset.sum_subset
  · intro m hm
    exact (Finsupp.finite_of_degree_le (σ:=σ) N).mem_toFinset.mpr ((le_totalDegree hm).trans hp)
  · intro m _ hm
    simp [notMem_support_iff.mp hm]

theorem realPolyEval_bounded_degree (p : MvPolynomial σ ℂ) (N : ℕ)
    (hp : p.totalDegree ≤ N) :
    realPolyEval p = fun x => ∑ m ∈ boundedDegreeMonomials (σ:=σ) N,
      p.coeff m • realPolyEval (monomial m 1) x := by
  classical
  conv_lhs => rw [bounded_degree_expansion p N hp]
  funext x
  simp [realPolyEval,smul_eq_mul,MvPolynomial.eval_monomial]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_polynomial_jets (P : X → MvPolynomial σ ℂ) (hP : CoeffContinuous P)
    (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N) (k : ℕ) :
    Continuous (fun q : X × (σ → ℝ) => iteratedFDeriv ℝ k (realPolyEval (P q.1)) q.2) := by
  classical
  have heq (p : X) (x : σ → ℝ) : iteratedFDeriv ℝ k (realPolyEval (P p)) x =
      ∑ m ∈ boundedDegreeMonomials (σ:=σ) N,
        (P p).coeff m • iteratedFDeriv ℝ k (realPolyEval (monomial m 1)) x := by
    rw [realPolyEval_bounded_degree (P p) N (hN p),iteratedFDeriv_fun_sum_apply
      (fun m _ => ((contDiff_realPolyEval (monomial m 1)).const_smul _).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) |>.contDiffAt)]
    apply Finset.sum_congr rfl
    intro m _
    exact iteratedFDeriv_const_smul_apply'
      ((contDiff_realPolyEval (monomial m 1)).of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))) |>.contDiffAt)
  simp only [heq]
  apply continuous_finsetSum
  intro m _
  exact ((hP m).comp continuous_fst).smul
    (((contDiff_realPolyEval (monomial m 1)).continuous_iteratedFDeriv (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)))).comp continuous_snd)

theorem compact_uniform_polynomial_jets (P : X → MvPolynomial σ ℂ)
    (hP : CoeffContinuous P) (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B) (k : ℕ) :
    ∃ C > 0, ∀ p ∈ K, ∀ x ∈ B, ‖iteratedFDeriv ℝ k (realPolyEval (P p)) x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hK.prod hB).exists_bound_of_continuousOn
    ((continuous_polynomial_jets P hP N hN k).continuousOn)
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro p hp x hx
  exact (hC (p,x) ⟨hp,hx⟩).trans (le_max_left _ _)



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

omit [Fintype σ] in
lemma CoeffContinuous.C {c : X → ℂ} (hc : Continuous c) :
    CoeffContinuous (fun x => MvPolynomial.C (c x) : X → MvPolynomial σ ℂ) := by
  intro m
  simp only [coeff_C]
  split_ifs
  · exact hc
  · exact continuous_const

lemma multilinearPolynomial_coeffContinuous {n : ℕ}
    (B : X → (σ → ℝ) [×n]→L[ℝ] ℂ) (hB : Continuous B) :
    CoeffContinuous (fun x => multilinearPolynomial (B x)) := by
  apply CoeffContinuous.sum Finset.univ
  intro a _
  apply CoeffContinuous.mul _ (CoeffContinuous.const _)
  apply CoeffContinuous.C
  exact hB.eval continuous_const

lemma realTaylorPolynomial_coeffContinuous (f : X → (σ → ℝ) → ℂ) (N : ℕ)
    (hf : ∀ k < N, Continuous (fun p => iteratedFDeriv ℝ k (f p) 0)) :
    CoeffContinuous (fun p => realTaylorPolynomial (f p) N) := by
  apply CoeffContinuous.sum (Finset.range N)
  intro k hk
  exact (CoeffContinuous.const _).mul
    (multilinearPolynomial_coeffContinuous _ (hf k (Finset.mem_range.mp hk)))

lemma wavePhaseSeed_coeffContinuous (c : X → ℂ) (hc : Continuous c)
    (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → σ → σ → ℂ) (hQ : ∀ i j, Continuous (fun p => Q p i j)) :
    CoeffContinuous (fun p => wavePhaseSeed (c p) (z p) (Q p)) := by
  exact ((CoeffContinuous.C hc).add
    (CoeffContinuous.sum Finset.univ _ (fun i _ => (CoeffContinuous.C (hz i)).mul
      (CoeffContinuous.const _)))).add
    ((CoeffContinuous.sum Finset.univ _ (fun i _ => CoeffContinuous.sum Finset.univ _
      (fun j _ => ((CoeffContinuous.C (hQ i j)).mul (CoeffContinuous.const _)).mul
        (CoeffContinuous.const _)))).smul continuous_const)

lemma smoothPhasePolynomial_coeffContinuous (g : X → σ → σ → (σ → ℝ) → ℂ)
    (c : X → ℂ) (hc : Continuous c) (z : X → σ → ℂ)
    (hz : ∀ i, Continuous (fun p => z p i)) (hz₀ : ∀ p, z p ≠ 0)
    (Q : X → σ → σ → ℂ) (hQ : ∀ i j, Continuous (fun p => Q p i j)) (L : ℕ)
    (hg : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0)) :
    CoeffContinuous (fun p => smoothPhasePolynomial (g p) (c p) (z p) (Q p) L) :=
  eikonalIter_coeffContinuous _
    (fun i j => realTaylorPolynomial_coeffContinuous _ L (hg i j)) z hz hz₀ _
    (wavePhaseSeed_coeffContinuous c hc z hz Q hQ) (L-2)

omit [DecidableEq σ] in
lemma wavePhaseSeed_degree (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) :
    (wavePhaseSeed c z Q).totalDegree ≤ 2 := by
  unfold wavePhaseSeed
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply totalDegree_finsetSum_le
      intro i _
      exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_smul_le _ _).trans
    apply totalDegree_finsetSum_le
    intro i _
    apply totalDegree_finsetSum_le
    intro j _
    exact (totalDegree_mul _ _).trans (by
      have h := totalDegree_mul (C (Q i j)) (MvPolynomial.X i)
      simp only [totalDegree_C, totalDegree_X, zero_add] at h ⊢
      omega)

lemma smoothPhasePolynomial_degree (g : σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hg0 : ∀ i j, g i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ i j, fderiv ℝ (g i j) 0 = 0)
    (c : ℂ) (z : σ → ℂ) (Q : σ → σ → ℂ) (hz : z ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hnull : ∑ i, z i * z i = -1)
    (hQz : ∀ k, ∑ i, z i * Q k i = 0) (L : ℕ) (hL : 2 ≤ L) :
    (smoothPhasePolynomial g c z Q L).totalDegree ≤ L :=
  (smoothPhasePolynomial_spec g hg hg0 hdg0 c z Q hz hQ hnull hQz L hL).2.2.2.trans
    (max_le ((wavePhaseSeed_degree c z Q).trans hL) le_rfl)


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

variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {X : Type*} [TopologicalSpace X]

omit [DecidableEq σ] in
lemma uniformJetBounds_realPolyEval (P : X → MvPolynomial σ ℂ)
    (hP : CoeffContinuous P) (N : ℕ) (hN : ∀ p, (P p).totalDegree ≤ N)
    {K : Set X} (hK : IsCompact K) {B : Set (σ → ℝ)} (hB : IsCompact B) :
    UniformJetBounds (fun p => realPolyEval (P p)) K B :=
  fun k => compact_uniform_polynomial_jets P hP N hN hK hB k

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
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_ComplexPolarWeight
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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff Matrix.Norms.Elementwise

lemma selectedComplexJetMatrix_leading (a ν b c d : PhaseSpace) (δ : ℝ) :
    selectedComplexJetMatrix (fun ℓ => leadingComplexJet
      (![complexPhaseVector a b,complexPhaseVector a c,
        complexPhaseVector (a+δ • ν) d] ℓ)) = physicalWaveJetMatrix a ν b c δ := by
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · fin_cases i; fin_cases j; simp [selectedComplexJetMatrix,leadingComplexJet,physicalWaveJetMatrix]
  · fin_cases j <;> simp [selectedComplexJetMatrix,leadingComplexJet,physicalWaveJetMatrix]
  · simp [selectedComplexJetMatrix,leadingComplexJet,complexPhaseVector,physicalWaveJetMatrix]
  · fin_cases j <;>
      simp [selectedComplexJetMatrix,leadingComplexJet,physicalWaveJetMatrix,complexPhaseVector,
        PiLp.add_apply,PiLp.smul_apply]

lemma selectedComplexJetMatrix_error (J K : Fin 3 → (Fin 1 ⊕ Fin 3) → ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hJ : ∀ ℓ, ‖J ℓ-K ℓ‖ ≤ ε) :
    ‖selectedComplexJetMatrix J-selectedComplexJetMatrix K‖ ≤ ε := by
  apply (Matrix.norm_le_iff hε).mpr
  intro i j
  have hr (ℓ) : |(J ℓ i).re-(K ℓ i).re| ≤ ε := by
    have hh := (Complex.abs_re_le_norm (J ℓ i-K ℓ i)).trans
      ((norm_le_pi_norm (J ℓ-K ℓ) i).trans (hJ ℓ))
    simpa only [Complex.sub_re] using hh
  have hi (ℓ) : |(J ℓ i).im-(K ℓ i).im| ≤ ε := by
    have hh := (Complex.abs_im_le_norm (J ℓ i-K ℓ i)).trans
      ((norm_le_pi_norm (J ℓ-K ℓ) i).trans (hJ ℓ))
    simpa only [Complex.sub_im] using hh
  rcases j with j|j
  · exact hr 0
  · fin_cases j
    · exact hr 2
    · exact hi 0
    · exact hi 1

lemma complexWaveJet_error (n : ℝ) (e : ℂ) (u : (Fin 3 → ℝ) → ℂ)
    (x : Fin 3 → ℝ) (z : Fin 3 → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hv : ‖e⁻¹*u x-1‖ ≤ ε)
    (hd : ‖fun i => (n : ℂ)⁻¹*e⁻¹*waveDeriv (Pi.single i 1) u x-z i‖ ≤ ε) :
    ‖complexWaveJet n e u x-leadingComplexJet z‖ ≤ ε := by
  apply (pi_norm_le_iff_of_nonneg hε).mpr
  intro i
  rcases i with i|i
  · exact hv
  · exact (norm_le_pi_norm _ i).trans hd


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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ENNReal Matrix.Norms.Elementwise

lemma complex_polar_weight (e : ℂ) (W : ℝ) :
    (Circle.exp (Complex.arg e) : ℂ)*(‖e‖/W : ℝ) = e/(W : ℂ) := by
  rw [Circle.coe_exp,Complex.ofReal_div]
  calc
    _ = ((‖e‖ : ℂ)*Complex.exp ((Complex.arg e : ℂ)*Complex.I))/(W : ℂ) := by ring
    _ = _ := by rw [Complex.norm_mul_exp_arg_mul_I]

lemma complexWaveJet_factor (n W : ℝ) (e : ℂ) (he : e ≠ 0)
    (u : (Fin 3 → ℝ) → ℂ) (x : Fin 3 → ℝ) :
    complexWaveJet n (W : ℂ) u x = fun i =>
      (Circle.exp (Complex.arg e) : ℂ)*((‖e‖/W : ℝ) : ℂ)*complexWaveJet n e u x i := by
  ext i
  rw [complex_polar_weight]
  rcases i with i|i
  · change (W : ℂ)⁻¹*u x = (e/(W:ℂ))*(e⁻¹*u x)
    calc
      _ = (e*e⁻¹)*((W : ℂ)⁻¹*u x) := by rw [mul_inv_cancel₀ he,one_mul]
      _ = _ := by ring
  · change (n : ℂ)⁻¹*(W : ℂ)⁻¹*waveDeriv (Pi.single i 1) u x =
      (e/(W:ℂ))*((n : ℂ)⁻¹*e⁻¹*waveDeriv (Pi.single i 1) u x)
    calc
      _ = (e*e⁻¹)*((n : ℂ)⁻¹*(W : ℂ)⁻¹*waveDeriv (Pi.single i 1) u x) := by
        rw [mul_inv_cancel₀ he,one_mul]
      _ = _ := by ring

lemma phase_weight_lower (c n φ R : ℝ) (hc : 0 < c) (hn : 1 ≤ n)
    (hR0 : 0 ≤ R) (hR : R ≤ n^6*Real.exp (n*φ)) (e : ℂ)
    (heB : c*Real.exp (n*φ) ≤ ‖e‖) :
    c/2*(n^6)⁻¹ ≤ ‖e‖/(Real.exp (n*φ)+R) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hn6 : 1 ≤ n^6 := one_le_pow₀ hn
  have hexp : 0 < Real.exp (n*φ) := Real.exp_pos _
  have hW : 0 < Real.exp (n*φ)+R := add_pos_of_pos_of_nonneg hexp hR0
  have hupper : Real.exp (n*φ)+R ≤ 2*n^6*Real.exp (n*φ) := by
    nlinarith [mul_le_mul_of_nonneg_right hn6 hexp.le]
  apply (le_div_iff₀ hW).mpr
  calc
    _ ≤ (c/2*(n^6)⁻¹)*(2*n^6*Real.exp (n*φ)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = c*Real.exp (n*φ) := by field_simp
    _ ≤ ‖e‖ := heB


end YauCounterexamples
end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Smoothness_UniformJetZeroDifference
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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section PhaseNearWeight
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma uniform_jet_zero_difference (S F : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hS0 : ∀ p, S p 0 = F p 0)
    (hSB : UniformJetBounds S univ (Metric.closedBall 0 1))
    (hFB : UniformJetBounds F univ (Metric.closedBall 0 1)) :
    ∃ C > 0, ∀ p x, x ∈ Metric.closedBall 0 1 → ‖S p x-F p x‖ ≤ C*‖x‖ := by
  obtain ⟨C1,hC1,hb1⟩ := hSB 1
  obtain ⟨C2,hC2,hb2⟩ := hFB 1
  refine ⟨C1+C2,add_pos hC1 hC2,?_⟩
  intro p x hx
  have hs : ‖S p x-S p 0‖ ≤ C1*‖x‖ := by
    have hh := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hS p).differentiable (by simp) y)
      (fun y hy => by simpa only [norm_iteratedFDeriv_one] using hb1 p (mem_univ _) y hy)
      (Metric.mem_closedBall_self zero_le_one) hx
    simpa only [sub_zero] using hh
  have hf : ‖F p x-F p 0‖ ≤ C2*‖x‖ := by
    have hh := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hF p).differentiable (by simp) y)
      (fun y hy => by simpa only [norm_iteratedFDeriv_one] using hb2 p (mem_univ _) y hy)
      (Metric.mem_closedBall_self zero_le_one) hx
    simpa only [sub_zero] using hh
  have he : S p x-F p x = (S p x-S p 0)-(F p x-F p 0) := by rw [hS0]; ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hs hf).trans_eq (by ring))

theorem phase_exp_near_weight (S F : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hS0 : ∀ p, S p 0 = F p 0)
    (hSB : UniformJetBounds S univ (Metric.closedBall 0 1))
    (hFB : UniformJetBounds F univ (Metric.closedBall 0 1)) :
    ∃ c > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : E, ‖x‖ ≤ 1/n →
      c*Real.exp (n*(F p x).re) ≤ ‖Complex.exp ((n : ℂ)*S p x)‖ := by
  obtain ⟨C,hC,hb⟩ := uniform_jet_zero_difference S F hS hF hS0 hSB hFB
  refine ⟨Real.exp (-C),Real.exp_pos _,?_⟩
  intro p n hn x hx
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hxball : x ∈ Metric.closedBall (0 : E) 1 := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact hx.trans (by simpa only [one_div] using (inv_le_one₀ hn0).mpr hn)
  have hh : ‖S p x-F p x‖ ≤ C/n :=
    (hb p x hxball).trans (by simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hx hC.le)
  have hre : (F p x).re-(S p x).re ≤ C/n := by
    have ht := Complex.re_le_norm (F p x-S p x)
    rw [Complex.sub_re,norm_sub_rev] at ht
    exact ht.trans hh
  have he : -C+n*(F p x).re ≤ n*(S p x).re := by
    have he' := (le_div_iff₀ hn0).mp hre
    nlinarith only [he']
  rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,←Real.exp_add]
  exact Real.exp_le_exp.mpr he

end PhaseNearWeight

end YauCounterexamples

end

end OAI
end

section
-- module Solutions.OAIQ070_YAU.SmoothYau_Estimates_CanonicalPhaseTripleSmallBall
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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology ContDiff

theorem all_admissible_waves_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb : ∀ p i, ContDiff ℝ ∞ (b p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ)
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (B C : ℝ) (κ : ℝ)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    ∃ r > 0, ∃ T > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ n : ℝ, 1 ≤ n → ∀ x : Fin 3 → ℝ, ‖x‖ < r → ‖x‖ ≤ 1/n →
        let S := realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q
          ((2*D+3*m+6)+(D+m+1)+1))
        let U := canonicalCutoffWave (g p) (b p) (φ p 0 : ℂ) z Q ζ m D n
        ‖(Complex.exp ((n : ℂ)*S x))⁻¹*U x-1‖ ≤ T/n ∧
        ‖fun i => (n : ℂ)⁻¹*(Complex.exp ((n : ℂ)*S x))⁻¹*
          waveDeriv (Pi.single i 1) U x-z i‖ ≤ T/n := by
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp
    (boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C)
  let base : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hbase : Continuous base := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hgc' (i j : Fin 3) (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (base q.1) i j) q.2) :=
    (hgc i j k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  have hbc' (i : Fin 3) (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (b (base q.1) i) q.2) :=
    (hbc i k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨r,hr,T,hT,h⟩ := generated_cutoff_waves_near_center
    (fun p : W => g (base p)) (fun p : W => b (base p))
    (fun p => hg (base p)) (fun p => hb (base p)) (fun p => hg0 (base p))
    (fun p => hdg0 (base p)) hgc' hbc' (fun p : W => (φ (base p) 0 : ℂ))
    (Complex.continuous_ofReal.comp (hφ0.comp hbase)) z
    (fun i => (continuous_apply i).comp hz) Q
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p : W => fun i j => congrFun (congrFun p.property.2.2.1 j) i) (fun p : W => p.property.2.1)
    (fun p : W => fun k => phase_matrix_annihilation _ _ p.property.2.2.2.1 k) ζ hζ m D
  refine ⟨r,hr,T,hT,?_⟩
  intro p z Q hz hn hQ n hn1 x hxr hx
  exact h ⟨((p,z),Q),hz,hn,hQ⟩ n hn1 x hxr hx


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
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff

theorem generated_phase_exp_near_center {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (s : X → ℂ) (hs : Continuous s) (z : X → Fin 3 → ℂ) (hz : ∀ i, Continuous (fun p => z p i))
    (Q : X → ComplexPhaseMatrix) (hQ : ∀ i j, Continuous (fun p => Q p i j))
    (hsym : ∀ p i j, Q p i j = Q p j i)
    (hnull : ∀ p, ∑ i, z p i*z p i = -1) (hQz : ∀ p k, ∑ i, z p i*Q p k i = 0)
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = s p)
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (L : ℕ) (hL : 2 ≤ L) :
    ∃ c > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : Fin 3 → ℝ, ‖x‖ ≤ 1/n →
      c*Real.exp (n*(F p x).re) ≤
        ‖Complex.exp ((n : ℂ)*realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) L) x)‖ := by
  let S := fun p => smoothPhasePolynomial (g p) (s p) (z p) (Q p) L
  have hz0 (p) : z p ≠ 0 := phase_vector_ne_zero _ (hnull p)
  have hSc : CoeffContinuous S := smoothPhasePolynomial_coeffContinuous g s hs z hz hz0 Q hQ L
    (fun i j k _ => (hgc i j k).comp (continuous_id.prodMk continuous_const))
  have hSd (p) : (S p).totalDegree ≤ L := smoothPhasePolynomial_degree (g p) (hg p)
    (hg0 p) (hdg0 p) (s p) (z p) (Q p) (hz0 p) (hsym p) (hnull p) (hQz p) L hL
  have hS0 (p) : realPolyEval (S p) 0 = F p 0 := by
    rw [hF0]
    have hh := (smoothPhasePolynomial_spec (g p) (hg p) (hg0 p) (hdg0 p) (s p) (z p)
      (Q p) (hz0 p) (hsym p) (hnull p) (hQz p) L hL).1.constantCoeff_eq_zero (by decide)
    have hc : constantCoeff (S p) = constantCoeff (wavePhaseSeed (s p) (z p) (Q p)) := by
      simpa only [map_sub,sub_eq_zero] using hh
    rw [realPolyEval_at_zero]
    exact hc.trans (wavePhaseSeed_constantCoeff (s p) (z p) (Q p))
  exact phase_exp_near_weight (fun p => realPolyEval (S p)) F (fun p => contDiff_realPolyEval _)
    hF hS0 (uniformJetBounds_realPolyEval S hSc L hSd isCompact_univ (isCompact_closedBall 0 1))
    (uniformJetBounds_of_continuous_jets F hFc isCompact_univ (isCompact_closedBall 0 1))

theorem all_admissible_phase_near_weight {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (φ : X → PhaseSpace → ℝ)
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (B C κ : ℝ) (L : ℕ) (hL : 2 ≤ L) :
    ∃ c > 0, ∀ p z Q, ‖z‖ ≤ B → (∑ i, z i*z i = -1) →
      PhaseMatrixValid (actualHessianForm (φ p)) z κ C Q →
      ∀ n : ℝ, 1 ≤ n → ∀ x : Fin 3 → ℝ, ‖x‖ ≤ 1/n →
      c*Real.exp (n*(F p x).re) ≤
        ‖Complex.exp ((n : ℂ)*realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) z Q L) x)‖ := by
  let H := fun p => actualHessianForm (φ p)
  let W := boundedPhaseSet H B κ C
  let : CompactSpace W := isCompact_iff_compactSpace.mp
    (boundedPhaseSet_isCompact H (continuous_actualHessianForm φ hφ2) B κ C)
  let base : W → X := fun p => p.val.1.1
  let z : W → Fin 3 → ℂ := fun p => p.val.1.2
  let Q : W → ComplexPhaseMatrix := fun p => p.val.2
  have hbase : Continuous base := (continuous_fst.comp continuous_fst).comp continuous_subtype_val
  have hz : Continuous z := (continuous_snd.comp continuous_fst).comp continuous_subtype_val
  have hQ : Continuous Q := continuous_snd.comp continuous_subtype_val
  have hgc' (i j : Fin 3) (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (g (base q.1) i j) q.2) :=
    (hgc i j k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  have hFc' (k : ℕ) : Continuous (fun q : W × (Fin 3 → ℝ) =>
      iteratedFDeriv ℝ k (F (base q.1)) q.2) :=
    (hFc k).comp ((hbase.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨c,hc,h⟩ := generated_phase_exp_near_center
    (fun p : W => g (base p)) (fun p => hg (base p)) (fun p => hg0 (base p))
    (fun p => hdg0 (base p)) hgc' (fun p : W => (φ (base p) 0 : ℂ))
    (Complex.continuous_ofReal.comp (hφ0.comp hbase)) z
    (fun i => (continuous_apply i).comp hz) Q
    (fun i j => (continuous_apply j).comp ((continuous_apply i).comp hQ))
    (fun p : W => fun i j => congrFun (congrFun p.property.2.2.1 j) i)
    (fun p : W => p.property.2.1)
    (fun p : W => fun k => phase_matrix_annihilation _ _ p.property.2.2.2.1 k)
    (fun p : W => F (base p)) (fun p => hF (base p)) (fun p => hF0 (base p)) hFc' L hL
  refine ⟨c,hc,?_⟩
  intro p z Q hz hn hQ n hn1 x hx
  exact h ⟨((p,z),Q),hz,hn,hQ⟩ n hn1 x hx

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
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise

theorem canonical_phase_triple_smallBall_oai {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (g : X → Fin 3 → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (b₀ : X → Fin 3 → (Fin 3 → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j)) (hb₀ : ∀ p i, ContDiff ℝ ∞ (b₀ p i))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (hgc : ∀ i j k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (g q.1 i j) q.2))
    (hbc : ∀ i k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (b₀ q.1 i) q.2))
    (φ : X → PhaseSpace → ℝ)
    (hφ0 : Continuous (fun p => φ p 0))
    (hφ2 : Continuous (fun q : X × PhaseSpace => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (F : X → (Fin 3 → ℝ) → ℂ) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hF0 : ∀ p, F p 0 = (φ p 0 : ℂ))
    (hFc : ∀ k, Continuous (fun q : X × (Fin 3 → ℝ) => iteratedFDeriv ℝ k (F q.1) q.2))
    (B C κ M η : ℝ) (hM : 1 ≤ M) (hη : 0 < η)
    (ζ : (Fin 3 → ℝ) → ℂ) (hζ : ζ =ᶠ[𝓝 0] fun _ => 1) (m D : ℕ) :
    ∃ r₀ > 0, ∃ c₀ > 0, ∃ ε > 0,
      ∀ p (n δ : ℝ), 1 ≤ n → 0 < δ → δ < ε → δ^2 = 1/n →
      ∀ a ν b c d : PhaseSpace, ‖a‖ ≤ M → ‖ν‖ = 1 →
        inner ℝ ν b = 0 → inner ℝ ν c = 0 →
        ‖b‖^2 = 1+‖a‖^2 → ‖c‖^2 = 1+‖a‖^2 →
        ‖b‖ ≤ M → ‖c‖ ≤ M → η ≤ transverseAngleSq b c →
      let z := ![complexPhaseVector a b,complexPhaseVector a c,
        complexPhaseVector (a+δ • ν) d]
      ∀ Q : Fin 3 → ComplexPhaseMatrix,
        (∀ ℓ, ‖z ℓ‖ ≤ B) → (∀ ℓ, ∑ i, z ℓ i*z ℓ i = -1) →
        (∀ ℓ, PhaseMatrixValid (actualHessianForm (φ p)) (z ℓ) κ C (Q ℓ)) →
      ∀ x : Fin 3 → ℝ, ‖x‖ < r₀ → ‖x‖ ≤ 1/n →
      ∀ R : ℝ, 0 ≤ R → R ≤ n^6*Real.exp (n*(F p x).re) →
      let W := Real.exp (n*(F p x).re)+R
      let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
      ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (noise : Ω → ((Fin 1 ⊕ Fin 3) → ℝ)), Measurable noise → ∀ r : ℝ, 0 ≤ r →
      (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
        {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
          Metric.closedBall 0 r} ≤
      ENNReal.ofReal (Real.sqrt η/2*δ*(c₀/2*(n^6)⁻¹)^4)⁻¹*(ENNReal.ofReal (2*r))^4 := by
  obtain ⟨r₀,hr₀,T,hT,hjets⟩ := all_admissible_waves_near_center g b₀ hg hb₀ hg0 hdg0 hgc hbc
    φ hφ0 hφ2 B C κ ζ hζ m D
  obtain ⟨c₀,hc₀,hweight⟩ := all_admissible_phase_near_weight g hg hg0 hdg0 hgc φ hφ0 hφ2
    F hF hF0 hFc B C κ ((2*D+3*m+6)+(D+m+1)+1) (by omega)
  obtain ⟨ε,hε,hsmall⟩ := physical_complex_wave_smallBall_uniform M T η hM hT.le hη
  refine ⟨r₀,hr₀,c₀,hc₀,ε,hε,?_⟩
  intro p n δ hn hδ hδε hδsq a ν b c d ha hν hb hc hbn hcn hbM hcM hang
  dsimp only at *
  intro Q hz hnull hQ x hxr hx R hR0 hR Ω _ μ _ noise hnoise r hr
  let z := ![complexPhaseVector a b,complexPhaseVector a c,complexPhaseVector (a+δ • ν) d]
  let U := fun ℓ => canonicalCutoffWave (g p) (b₀ p) (φ p 0 : ℂ) (z ℓ) (Q ℓ) ζ m D n
  let S := fun ℓ => realPolyEval (smoothPhasePolynomial (g p) (φ p 0 : ℂ) (z ℓ) (Q ℓ)
    ((2*D+3*m+6)+(D+m+1)+1))
  let e := fun ℓ => Complex.exp ((n : ℂ)*S ℓ x)
  let W := Real.exp (n*(F p x).re)+R
  let w := fun ℓ => ‖e ℓ‖/W
  let J := fun ℓ => complexWaveJet n (e ℓ) (U ℓ) x
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hJ : ‖selectedComplexJetMatrix J-physicalWaveJetMatrix a ν b c δ‖ ≤ T*δ^2 := by
    rw [← selectedComplexJetMatrix_leading a ν b c d δ,hδsq]
    have heq : T*(1/n) = T/n := by ring
    rw [heq]
    apply selectedComplexJetMatrix_error _ _ _ (div_nonneg hT.le hn0.le)
    intro ℓ
    obtain ⟨hv,hd⟩ := hjets p (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ) n hn x hxr hx
    exact complexWaveJet_error n (e ℓ) (U ℓ) x (z ℓ) _ (div_nonneg hT.le hn0.le) hv hd
  have hw (ℓ) : c₀/2*(n^6)⁻¹ ≤ w ℓ :=
    phase_weight_lower c₀ n (F p x).re R hc₀ hn hR0 hR (e ℓ)
      (hweight p (z ℓ) (Q ℓ) (hz ℓ) (hnull ℓ) (hQ ℓ) n hn x hx)
  have hf : (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) =
      (fun ℓ i => (Circle.exp (Complex.arg (e ℓ)) : ℂ)*((w ℓ : ℂ)*J ℓ i)) := by
    funext ℓ i
    rw [complexWaveJet_factor n W (e ℓ) (Complex.exp_ne_zero _) (U ℓ) x]
    exact mul_assoc _ _ _
  change (μ.prod (Measure.pi (fun _ : Fin 3 => stdGaussian ℂ)))
    {v | complexRealResponse (fun ℓ => complexWaveJet n (W : ℂ) (U ℓ) x) v.2+noise v.1 ∈
      Metric.closedBall 0 r} ≤ _
  rw [hf]
  exact hsmall δ hδ hδε a ν b c ha hν hb hc hbn hcn hbM hcM hang J hJ
    (c₀/2*(n^6)⁻¹) (by positivity) w hw (fun ℓ => Circle.exp (Complex.arg (e ℓ)))
    Ω μ noise hnoise r hr



end YauCounterexamples
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.YauCounterexamples.canonical_phase_triple_smallBall_oai.{u_1, u_2} := @OAI.YauCounterexamples.canonical_phase_triple_smallBall_oai.{u_1, u_2}
