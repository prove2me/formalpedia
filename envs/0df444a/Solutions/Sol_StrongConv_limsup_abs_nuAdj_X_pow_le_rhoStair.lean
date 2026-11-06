-- Prove2me | solution 1 for StrongConv.limsup_abs_nuAdj_X_pow_le_rhoStair
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:02:03.026778+00:00
-- url     : https://prove2.me/submissions/d3b6fc48-6a46-4e51-a014-c4579a19822b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_StrongConv
import Definitions.Def_StrongConvPuder
import Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval
import Theorems.Thm_StrongConv_exists_uniformExp_trN_wordEval_eq_div
import Theorems.Thm_Puder_wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le
import Theorems.Thm_Puder_limsup_sum_ncard_crit_rpow_eq_rhoStair
import Mathlib

section
section
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5

/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

/-- Number of fixed points. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card


end StrongConv.S5
end
end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartPerm

open scoped InnerProductSpace

lemma permOp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : EuclideanSpace ℂ (Fin N)) (j : Fin N) :
    permOp π x j = x (π.symm j) := by
  simp [permOp, LinearIsometryEquiv.piLpCongrLeft_apply]

lemma permOp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOp (π * ρ) = permOp π * permOp ρ := by
  ext x j
  simp only [permOp_apply, mul_apply_eq_comp]
  rfl

lemma permOp_one {N : ℕ} : permOp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x j
  simp only [permOp_apply]
  rfl

lemma permOpPerp_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : OnesPerp N) :
    (permOpPerp π x : EuclideanSpace ℂ (Fin N)) = permOp π x := rfl

lemma permOpPerp_mul {N : ℕ} (π ρ : Equiv.Perm (Fin N)) :
    permOpPerp (π * ρ) = permOpPerp π * permOpPerp ρ := by
  ext x : 2
  simp [permOpPerp_apply, permOp_mul]

lemma permOpPerp_one {N : ℕ} : permOpPerp (1 : Equiv.Perm (Fin N)) = 1 := by
  ext x : 2
  simp [permOpPerp_apply, permOp_one]

lemma inner_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℂ (Fin N)) :
    ⟪permOp π x, y⟫_ℂ = ⟪x, permOp π⁻¹ y⟫_ℂ := by
  have : y = permOp π (permOp π⁻¹ y) := by
    rw [← mul_apply_eq_comp, ← permOp_mul, mul_inv_cancel, permOp_one]; rfl
  conv_lhs => rw [this]
  exact LinearIsometryEquiv.inner_map_map _ _ _

lemma star_permOpPerp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    star (permOpPerp π) = permOpPerp π⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [Submodule.coe_inner, permOpPerp_apply]
  rw [inner_permOp, inv_inv]

lemma wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordEval (sModel σ) w = permOpPerp (wordPerm σ w) := by
  induction w with
  | nil => simp [wordEval, wordPerm, permOpPerp_one]
  | cons a w ih =>
    simp only [wordEval, wordPerm, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, permOpPerp_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [letterPerm, permOpPerp_one]
    · simp [letterPerm, letterOp, sModel]
    · simp [letterPerm, letterOp, sModel, star_permOpPerp]

lemma trace_permOp {N : ℕ} (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) = (fixCount π : ℂ) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (PiLp.basisFun 2 ℂ (Fin N)), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, PiLp.basisFun_apply, PiLp.basisFun_repr,
    ContinuousLinearMap.coe_coe, permOp_apply]
  rw [fixCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (π.symm i = i) ↔ (π i = i) := by
    rw [Equiv.symm_apply_eq, eq_comm]
  by_cases h : π i = i
  · simp [h, this.mpr h]
  · simp [h, mt this.mp h]

lemma trace_eq_add_of_isCompl {M : Type*} [AddCommGroup M] [Module ℂ M]
    [FiniteDimensional ℂ M] (p q : Submodule ℂ M) (h : IsCompl p q) (f : M →ₗ[ℂ] M)
    (hp : Set.MapsTo f p p) (hq : Set.MapsTo f q q) :
    LinearMap.trace ℂ M f = LinearMap.trace ℂ p (f.restrict hp) +
      LinearMap.trace ℂ q (f.restrict hq) := by
  let A : Fin 2 → Submodule ℂ M := ![p, q]
  have hA : DirectSum.IsInternal A :=
    (DirectSum.isInternal_submodule_iff_isCompl A (i := 0) (j := 1) (by decide)
      (by ext k; fin_cases k <;> simp)).mpr h
  have hf : ∀ i, Set.MapsTo f (A i) (A i) := by
    intro i; fin_cases i
    · exact hp
    · exact hq
  rw [LinearMap.trace_eq_sum_trace_restrict hA hf, Fin.sum_univ_two]
  rfl

lemma trace_permOpPerp {N : ℕ} (hN : 1 ≤ N) (π : Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ _ ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) = (fixCount π : ℂ) - 1 := by
  set K : Submodule ℂ (EuclideanSpace ℂ (Fin N)) := ℂ ∙ onesVec N with hK
  have hones : permOp π (onesVec N) = onesVec N := by
    ext j; simp [permOp_apply, onesVec]
  have hp : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) K K := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp only [ContinuousLinearMap.coe_coe, map_smul, hones]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hq : Set.MapsTo ((permOp π : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
      EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)) Kᗮ Kᗮ := by
    intro x hx
    exact (permOpPerp π ⟨x, hx⟩).2
  have h := trace_eq_add_of_isCompl K Kᗮ (Submodule.isCompl_orthogonal K)
    _ hp hq
  rw [trace_permOp] at h
  have h1 : LinearMap.restrict _ hp = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    apply Subtype.ext
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    show permOp π (c • onesVec N) = c • onesVec N
    rw [map_smul, hones]
  have h2 : LinearMap.restrict _ hq = ((permOpPerp π : OnesPerp N →L[ℂ] OnesPerp N) :
      OnesPerp N →ₗ[ℂ] OnesPerp N) := by
    ext x; rfl
  have hne : onesVec N ≠ 0 := by
    intro h0
    have := congr_arg (fun v : EuclideanSpace ℂ (Fin N) => v ⟨0, hN⟩) h0
    simp [onesVec] at this
  have hr : Module.finrank ℂ K = 1 := finrank_span_singleton hne
  rw [h1, h2, LinearMap.trace_id, hr] at h
  rw [h]
  push_cast
  ring

theorem wordPerm_eq_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    wordPerm σ w = FreeGroup.lift σ (wordFree w) := by
  induction w with
  | nil => simp [wordPerm, wordFree]
  | cons a w ih =>
    simp only [wordPerm, wordFree, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases a with _ | (i | i) <;> simp [letterPerm]

theorem trN_wordEval_sModel {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    trN N (wordEval (sModel σ) w) = ((fixCount (wordPerm σ w) : ℝ) - 1) / N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [trN]
  rw [trN, wordEval_sModel, trace_permOpPerp hN]
  simp

/-! ### The left-regular representation -/

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma leftReg_mul {d : ℕ} (g g' : FreeGroup (Fin d)) :
    leftReg (g * g') = leftReg g * leftReg g' := by
  ext f h
  simp only [leftReg_apply, mul_apply_eq_comp, mul_inv_rev, mul_assoc]

lemma leftReg_one {d : ℕ} : leftReg (1 : FreeGroup (Fin d)) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    wordEval (sLimit d) w = leftReg (wordFree w) := by
  induction w with
  | nil => simp [wordEval, wordFree, leftReg_one]
  | cons a w ih =>
    simp only [wordEval, wordFree, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, leftReg_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [leftReg_one]
    · simp [letterOp, sLimit]
    · simp [letterOp, sLimit, star_leftReg]

theorem tau_wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    tau (wordEval (sLimit d) w) = if wordFree w = 1 then 1 else 0 := by
  classical
  rw [wordEval_sLimit, tau, delta, lp.inner_single_left, leftReg_apply]
  simp only [mul_one, lp.single_apply]
  by_cases h : wordFree w = 1
  · simp [h]
  · rw [if_neg h, Pi.single_apply, if_neg (by simpa [inv_eq_one] using h)]
    simp

end StrongConv.S5.PartPerm


open Polynomial Filter Topology

noncomputable section

namespace StrongConv.L82

open StrongConv

section Alg
variable {R ι : Type*} [Ring R] [Fintype ι]

lemma sum_pow_words (f : ι → R) (p : ℕ) :
    (∑ i, f i) ^ p = ∑ x : Fin p → ι, (List.ofFn fun j => f (x j)).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (p + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp [Fin.consEquiv, List.ofFn_succ]

end Alg


section Op
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma adj_sum {d : ℕ} (u : Fin d → H →L[ℂ] H) :
    ∑ i, (u i + star (u i)) = ∑ l : Fin d ⊕ Fin d, letterOp u l := by
  rw [Fintype.sum_sum_type]; simp [letterOp, Finset.sum_add_distrib]

lemma wordEval_ofFn {d p : ℕ} (u : Fin d → H →L[ℂ] H) (x : Fin p → Fin d ⊕ Fin d) :
    wordEval u (List.ofFn fun j => some (x j)) = (List.ofFn fun j => letterOp u (x j)).prod := by
  simp [wordEval, List.map_ofFn, Function.comp_def]

lemma adj_pow {d : ℕ} (u : Fin d → H →L[ℂ] H) (p : ℕ) :
    (∑ i, (u i + star (u i))) ^ p =
      ∑ x : Fin p → Fin d ⊕ Fin d, wordEval u (List.ofFn fun j => some (x j)) := by
  rw [adj_sum, sum_pow_words]
  simp_rw [wordEval_ofFn]

lemma isSA_adj {d : ℕ} (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (∑ i, (u i + star (u i))) := by
  unfold IsSelfAdjoint
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_add, star_star, add_comm]

end Op

lemma fnCalc_pow {A : Type*} [CStarAlgebra A] (T : A) (hT : IsSelfAdjoint T) (p : ℕ) :
    fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) T = T ^ p := by
  unfold fnCalc
  rw [← cfc_pow_id (R := ℂ) T p]
  refine cfc_congr (fun z hz => ?_)
  have := hT.mem_spectrum_eq_re hz
  simp only [eval_pow, eval_X, Complex.ofReal_pow]
  rw [← this]


lemma trN_sum {N : ℕ} {ι : Type*} (s : Finset ι) (Y : ι → (OnesPerp N →L[ℂ] OnesPerp N)) :
    trN N (∑ x ∈ s, Y x) = ∑ x ∈ s, trN N (Y x) := by
  unfold trN
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum, Complex.re_sum, Finset.sum_div]

lemma uniformExp_sum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (f : ι → X → ℝ) :
    uniformExp (fun a => ∑ x ∈ s, f x a) = ∑ x ∈ s, uniformExp (f x) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]

/-- the word of letters `x` -/
def wd {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) : List (Letter d) := List.ofFn fun j => some (x j)

/-- `E tr_N` of the word -/
def aN {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) (N : ℕ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) (wd x)))

lemma F_eq (d p N : ℕ) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ))) =
      ∑ x : Fin p → Fin d ⊕ Fin d, aN x N := by
  have h : ∀ σ : Fin d → Equiv.Perm (Fin N),
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ)) =
        ∑ x : Fin p → Fin d ⊕ Fin d, trN N (wordEval (sModel σ) (wd x)) := by
    intro σ
    unfold adjPerp
    rw [fnCalc_pow _ (isSA_adj (sModel σ)) p, adj_pow, trN_sum]
    rfl
  simp_rw [h]
  rw [uniformExp_sum]
  rfl



section Limits


end Limits

end StrongConv.L82
end

end
end
end
end

section
section
open Polynomial Filter Topology Asymptotics

noncomputable section

namespace StrongConv.L85

/-- `F` has the full asymptotic expansion `∑ cᵢ / Nⁱ`. -/
def HasExp (F : ℕ → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, Tendsto (fun N : ℕ => (N : ℝ) ^ m * (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i))
    atTop (𝓝 (c m))

lemma asympCoeff_eq {F c : ℕ → ℝ} (hF : HasExp F c) (m : ℕ) : asympCoeff F m = c m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [asympCoeff]
    have h : ∀ N : ℕ, ∑ i : Fin m, asympCoeff F i / (N : ℝ) ^ (i : ℕ) =
        ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i := by
      intro N
      rw [← Fin.sum_univ_eq_sum_range (fun i => c i / (N : ℝ) ^ i) m]
      exact Finset.sum_congr rfl (fun i _ => by rw [ih i i.isLt])
    simp_rw [h]
    exact (hF m).limUnder_eq

lemma HasExp.congr_eventually {F G c : ℕ → ℝ} (hG : HasExp G c) (h : ∀ᶠ N : ℕ in atTop, F N = G N) :
    HasExp F c := by
  intro m
  refine (hG m).congr' ?_
  filter_upwards [h] with N hN
  rw [hN]

lemma HasExp.sum {ι : Type*} (s : Finset ι) {F : ι → ℕ → ℝ} {c : ι → ℕ → ℝ}
    (h : ∀ i ∈ s, HasExp (F i) (c i)) :
    HasExp (fun N => ∑ i ∈ s, F i N) (fun m => ∑ i ∈ s, c i m) := by
  intro m
  have := tendsto_finsetSum s (fun i hi => h i hi m)
  refine this.congr (fun N => ?_)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  congr 2
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]

lemma HasExp.unique {F c c' : ℕ → ℝ} (h : HasExp F c) (h' : HasExp F c') (m : ℕ) : c m = c' m := by
  rw [← asympCoeff_eq h, ← asympCoeff_eq h']

/-- multiplying by `N` shifts the expansion, when the constant term vanishes -/
lemma HasExp.shift {F c : ℕ → ℝ} (h : HasExp F c) (h0 : c 0 = 0) :
    HasExp (fun N => (N : ℝ) * F N) (fun s => c (s + 1)) := by
  intro m
  refine (h (m + 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  rw [Finset.sum_range_succ', h0, zero_div, add_zero]
  have : (N : ℝ) ^ (m + 1) * ∑ i ∈ Finset.range m, c (i + 1) / (N : ℝ) ^ (i + 1) =
      (N : ℝ) ^ m * ∑ i ∈ Finset.range m, c (i + 1) / (N : ℝ) ^ i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
    ring
  rw [mul_sub, this, pow_succ, mul_sub]
  ring

/-- Rational functions of `1/N` with nonvanishing denominator at `0` have full expansions. -/
lemma exists_hasExp_of_rational (f g : ℝ[X]) (hg : g.eval 0 ≠ 0) (F : ℕ → ℝ)
    (hF : ∀ᶠ N : ℕ in atTop, F N = f.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ))) :
    ∃ c, HasExp F c := by
  have hf : AnalyticAt ℝ (fun x : ℝ => f.eval x) 0 :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) f) 0 (Set.mem_univ _)
  have hg' : AnalyticAt ℝ (fun x : ℝ => g.eval x) 0 :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) g) 0 (Set.mem_univ _)
  have hφ : AnalyticAt ℝ (fun x : ℝ => f.eval x / g.eval x) 0 := hf.div hg' hg
  obtain ⟨p, hp⟩ := hφ
  refine ⟨fun k => p.coeff k, ?_⟩
  have hbig := fun n => hp.isBigO_sub_partialSum_pow n
  have hy : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    exact tendsto_one_div_atTop_nhds_zero_nat
  apply HasExp.congr_eventually (G := fun N : ℕ => f.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ))) _ hF
  intro m
  have h1 := ((hbig (m + 1)).comp_tendsto hy)
  have h2 : (fun N : ℕ => (N : ℝ) ^ m * ((fun y : ℝ => f.eval (0 + y) / g.eval (0 + y) -
      p.partialSum (m + 1) y) (1 / (N : ℝ)))) =O[atTop] fun N : ℕ => 1 / (N : ℝ) := by
    have := (Asymptotics.isBigO_refl (fun N : ℕ => (N : ℝ) ^ m) atTop).mul h1
    refine this.trans ?_
    refine (isBigO_of_le _ (fun N => ?_))
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [Function.comp, norm_mul, norm_pow, Real.norm_natCast, Real.norm_eq_abs, norm_div,
      norm_one, abs_of_pos hN', one_div, norm_inv, abs_inv]
    apply le_of_eq
    rw [pow_succ]
    field_simp
    rw [← mul_pow, mul_one_div_cancel hN'.ne', one_pow]
  have h3 : Tendsto (fun N : ℕ => (N : ℝ) ^ m * ((fun y : ℝ => f.eval (0 + y) / g.eval (0 + y) -
      p.partialSum (m + 1) y) (1 / (N : ℝ)))) atTop (𝓝 0) :=
    h2.trans_tendsto hy
  have h4 := h3.add_const (p.coeff m)
  rw [zero_add] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, zero_add]
  have key : (N : ℝ) ^ m * ((N : ℝ)⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hN0, one_pow]
  have e : ∀ x : ℕ, p.coeff x / (N : ℝ) ^ x = ((N : ℝ)⁻¹) ^ x * p.coeff x := by
    intro x; rw [inv_pow]; ring
  simp_rw [e, one_div]
  linear_combination (-(p.coeff m)) * key

end StrongConv.L85

end

end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.L85
open StrongConv

/-- `E tr_N w(Sᴺ)` -/
def Ew (d : ℕ) (w : List (Letter d)) (N : ℕ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) w))

lemma exists_hasExp (d : ℕ) (w : List (Letter d)) : ∃ c, HasExp (Ew d w) c := by
  obtain ⟨_, f, _, hf⟩ := exists_uniformExp_trN_wordEval_eq_div d (w.length + 1) (by omega) w
    (by omega)
  refine exists_hasExp_of_rational f (gPoly d (w.length + 1)) ?_ _ ?_
  · simp [gPoly, Polynomial.eval_prod]
  · filter_upwards [eventually_ge_atTop (w.length + 1)] with N hN
    exact hf N hN

/-- the expansion coefficients of `E tr_N w(Sᴺ)` -/
def cw (d : ℕ) (w : List (Letter d)) : ℕ → ℝ := Classical.choose (exists_hasExp d w)

lemma hasExp_cw (d : ℕ) (w : List (Letter d)) : HasExp (Ew d w) (cw d w) :=
  Classical.choose_spec (exists_hasExp d w)

lemma tendsto_Ew (d : ℕ) (w : List (Letter d)) :
    Tendsto (Ew d w) atTop (𝓝 (if wordFree w = 1 then 1 else 0)) := by
  have h := tendsto_uniformExp_trN_wordEval d w
  have h2 := (Complex.continuous_re.tendsto _).comp h
  rw [S5.PartPerm.tau_wordEval_sLimit] at h2
  have e : (if wordFree w = 1 then (1 : ℂ) else 0).re = if wordFree w = 1 then 1 else 0 := by
    split_ifs <;> simp
  rw [Function.comp_def, e] at h2
  exact h2

lemma cw_zero {d : ℕ} {w : List (Letter d)} (hw : wordFree w ≠ 1) : cw d w 0 = 0 := by
  have h1 := hasExp_cw d w 0
  simp only [pow_zero, Finset.range_zero, Finset.sum_empty, sub_zero, one_mul] at h1
  have h2 := tendsto_Ew d w
  rw [if_neg hw] at h2
  exact tendsto_nhds_unique h1 h2

lemma wordCoeff_eq {d : ℕ} {w : List (Letter d)} (hw : wordFree w ≠ 1) (s : ℕ) :
    wordCoeff w s = cw d w (s + 1) :=
  asympCoeff_eq ((hasExp_cw d w).shift (cw_zero hw)) s

lemma Ew_one {d : ℕ} {w : List (Letter d)} (hw : wordFree w = 1) {N : ℕ} (hN : 1 ≤ N) :
    Ew d w N = ((N : ℝ) - 1) / N := by
  have h : ∀ σ : Fin d → Equiv.Perm (Fin N),
      trN N (wordEval (sModel σ) w) = ((N : ℝ) - 1) / N := by
    intro σ
    rw [S5.PartPerm.trN_wordEval_sModel, S5.PartPerm.wordPerm_eq_lift]
    rw [hw, map_one]
    simp [S5.fixCount]
  unfold Ew
  simp_rw [h]
  unfold uniformExp
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin d → Equiv.Perm (Fin N)) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp

/-- coefficients of `1 - 1/N` -/
def c1 (k : ℕ) : ℝ := if k = 0 then 1 else if k = 1 then -1 else 0

lemma sum_c1 (N : ℕ) (hN : (N : ℝ) ≠ 0) (k : ℕ) :
    ∑ i ∈ Finset.range (k + 2), c1 i / (N : ℝ) ^ i = 1 - 1 / N := by
  induction k with
  | zero => simp [Finset.sum_range_succ, c1]; ring
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp [c1]

lemma hasExp_free : HasExp (fun N : ℕ => ((N : ℝ) - 1) / N) c1 := by
  intro m
  rcases m with _ | _ | k
  · simp only [pow_zero, Finset.range_zero, Finset.sum_empty, sub_zero, one_mul, c1, if_true]
    have : Tendsto (fun N : ℕ => 1 - 1 / (N : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
  · simp only [c1, zero_add, pow_one, Finset.sum_range_one, if_true, pow_zero, div_one]
    simp only [one_ne_zero, if_false]
    refine (tendsto_const_nhds (x := (-1 : ℝ))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    field_simp
    ring
  · have : c1 (k + 1 + 1) = 0 := by simp [c1]
    rw [this]
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    rw [sum_c1 N hN0 k]
    field_simp
    ring

lemma cw_free {d : ℕ} {w : List (Letter d)} (hw : wordFree w = 1) {m : ℕ} (hm : 2 ≤ m) :
    cw d w m = 0 := by
  have h : HasExp (Ew d w) c1 := by
    refine hasExp_free.congr_eventually ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact Ew_one hw hN
  rw [(hasExp_cw d w).unique h m]
  unfold c1
  rw [if_neg (by omega), if_neg (by omega)]

/-- the letters-words of length `p` -/
def wdd {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) : List (Letter d) :=
  List.ofFn fun j => some (x j)

lemma nuAdj_eq_sum (d p m : ℕ) (hm : 2 ≤ m) :
    nuAdj d m ((X : ℝ[X]) ^ p) = ∑ x : Fin p → Fin d ⊕ Fin d,
      (if wordFree (wdd x) = 1 then 0 else wordCoeff (wdd x) (m - 1)) := by
  set Fp : ℕ → ℝ := fun N => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ))) with hFp
  have hF : ∀ N, Fp N = ∑ x : Fin p → Fin d ⊕ Fin d, Ew d (wdd x) N := fun N => L82.F_eq d p N
  have hE : HasExp Fp (fun k => ∑ x : Fin p → Fin d ⊕ Fin d, cw d (wdd x) k) := by
    have := HasExp.sum Finset.univ (fun (x : Fin p → Fin d ⊕ Fin d) _ => hasExp_cw d (wdd x))
    have e : Fp = fun N => ∑ x : Fin p → Fin d ⊕ Fin d, Ew d (wdd x) N := funext hF
    rw [e]
    exact this
  show asympCoeff Fp m = _
  rw [asympCoeff_eq hE m]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs with h
  · exact cw_free h hm
  · rw [wordCoeff_eq h]
    congr 1
    omega

end StrongConv.L85

end

end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.L85
open StrongConv Puder

lemma exists_crit {d : ℕ} {w : FreeGroup (Fin d)} (h : primitivityRank w ≠ ⊤) :
    (Crit w).Nonempty := by
  classical
  have hex : ∃ r' : ℕ, ∃ J : Subgroup (FreeGroup (Fin d)), w ∈ J ∧ HasRank J r' ∧
      ¬ IsPrimitiveIn J w := by
    by_contra hne
    push Not at hne
    apply h
    simp [primitivityRank]
    exact hne
  have hspec := Nat.find_spec hex
  have heq : primitivityRank w = (Nat.find hex : ℕ∞) := by
    apply le_antisymm
    · exact iInf₂_le (Nat.find hex) hspec
    · exact le_iInf₂ fun r' hr' => Nat.cast_le.2 (Nat.find_min' hex hr')
  obtain ⟨J, hJ1, hJ2, hJ3⟩ := hspec
  exact ⟨J, hJ1, hJ3, Nat.find hex, hJ2, heq.symm⟩

/-- the Puder sum -/
def S (d p : ℕ) (r : ℕ) : ℝ :=
  ∑ i : Fin p → Fin d ⊕ Fin d with
      primitivityRank (StrongConv.wordFree (List.ofFn fun j => some (i j))) = r,
    ((Crit (StrongConv.wordFree (List.ofFn fun j => some (i j)))).ncard : ℝ)

lemma abs_term_le (d p m : ℕ) (hp : 1 ≤ p) (hm : 1 ≤ m) (x : Fin p → Fin d ⊕ Fin d)
    (hx : wordFree (wdd x) ≠ 1) :
    |wordCoeff (wdd x) (m - 1)| ≤ ∑ r ∈ Finset.range (m + 1),
      (if primitivityRank (wordFree (wdd x)) = (r : ℕ∞)
        then (p : ℝ) ^ (2 * m) * ((Crit (wordFree (wdd x))).ncard : ℝ) else 0) := by
  classical
  obtain ⟨h1, h2, h3, -⟩ := wordCoeff_eq_zero_and_eq_ncard_crit_and_abs_le d (wdd x) hx
  have hlen : ((wdd x).length : ℝ) = p := by simp [wdd]
  have hnn : ∀ r ∈ Finset.range (m + 1),
      0 ≤ (if primitivityRank (wordFree (wdd x)) = (r : ℕ∞)
        then (p : ℝ) ^ (2 * m) * ((Crit (wordFree (wdd x))).ncard : ℝ) else 0) := by
    intro r _
    split_ifs <;> positivity
  by_cases hlt : (((m - 1 : ℕ) : ℕ∞) + 2 ≤ primitivityRank (wordFree (wdd x)))
  · rw [h1 _ hlt, abs_zero]
    exact Finset.sum_nonneg hnn
  · push Not at hlt
    have hne : primitivityRank (wordFree (wdd x)) ≠ ⊤ := by
      intro h; rw [h] at hlt; simp at hlt
    obtain ⟨r0, hr0⟩ := ENat.ne_top_iff_exists.1 hne
    have hr0' : primitivityRank (wordFree (wdd x)) = (r0 : ℕ∞) := hr0.symm
    have hr0m : r0 < m - 1 + 2 := by
      rw [hr0'] at hlt
      exact_mod_cast hlt
    obtain ⟨hfin, hcoef⟩ := h2 r0 hr0'
    have hcard : 1 ≤ (Crit (wordFree (wdd x))).ncard :=
      Nat.succ_le_of_lt ((Set.ncard_pos hfin).2 (exists_crit hne))
    · have hcardR : (1 : ℝ) ≤ ((Crit (wordFree (wdd x))).ncard : ℝ) := by exact_mod_cast hcard
      have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ (2 * m) := one_le_pow₀ (by exact_mod_cast hp)
      have hterm : (p : ℝ) ^ (2 * m) * ((Crit (wordFree (wdd x))).ncard : ℝ) ≤
          ∑ r ∈ Finset.range (m + 1),
            (if primitivityRank (wordFree (wdd x)) = (r : ℕ∞)
              then (p : ℝ) ^ (2 * m) * ((Crit (wordFree (wdd x))).ncard : ℝ) else 0) := by
        have hmem : r0 ∈ Finset.range (m + 1) := by simp; omega
        calc _ = (if primitivityRank (wordFree (wdd x)) = (r0 : ℕ∞)
              then (p : ℝ) ^ (2 * m) * ((Crit (wordFree (wdd x))).ncard : ℝ) else 0) := by
                rw [if_pos hr0']
          _ ≤ _ := Finset.single_le_sum hnn hmem
      refine le_trans ?_ hterm
      by_cases hrm : r0 = m
      · subst hrm
        rw [hcoef, abs_of_nonneg (by positivity)]
        nlinarith
      · have hle : primitivityRank (wordFree (wdd x)) ≤ ((m - 1 : ℕ) : ℕ∞) := by
          rw [hr0']; exact_mod_cast (by omega : r0 ≤ m - 1)
        have := h3 (m - 1) hle
        rw [hlen] at this
        have e : 2 * (m - 1 + 1) = 2 * m := by omega
        rw [e] at this
        nlinarith

end StrongConv.L85

end

end
end

section
section
open Polynomial Filter Topology

noncomputable section

namespace StrongConv.L85
open StrongConv Puder

lemma abs_nuAdj_le (d p m : ℕ) (hp : 1 ≤ p) (hm : 2 ≤ m) :
    |nuAdj d m ((X : ℝ[X]) ^ p)| ≤ (p : ℝ) ^ (2 * m) * ∑ r ∈ Finset.range (m + 1), S d p r := by
  classical
  rw [nuAdj_eq_sum d p m hm]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ x : Fin p → Fin d ⊕ Fin d,
      |(if wordFree (wdd x) = 1 then 0 else wordCoeff (wdd x) (m - 1))| ≤
        ∑ r ∈ Finset.range (m + 1),
          (if primitivityRank (wordFree (wdd x)) = (r : ℕ∞)
            then (p : ℝ) ^ (2 * m) * ((Crit (wordFree (wdd x))).ncard : ℝ) else 0) := by
    intro x
    split_ifs with h
    · rw [abs_zero]
      exact Finset.sum_nonneg (fun r _ => by split_ifs <;> positivity)
    · exact abs_term_le d p m hp (by omega) x h
  refine (Finset.sum_le_sum (fun x _ => hterm x)).trans (le_of_eq ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [S, ← Finset.sum_filter, ← Finset.mul_sum]
  rfl

lemma rhoStair_mono {d r m : ℕ} (hd : 2 ≤ d) (hrm : r ≤ m) : rhoStair d r ≤ rhoStair d m := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) ≤ 2 * d - 1 := by linarith
  set s := Real.sqrt (2 * d - 1) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = 2 * d - 1 := Real.sq_sqrt hpos
  have hrmR : (r : ℝ) ≤ m := by exact_mod_cast hrm
  unfold rhoStair
  rw [← hsdef]
  split_ifs with h1 h2 h2
  · exact le_refl _
  · -- t_m > s
    have ht : s < 2 * (m : ℝ) - 1 := not_le.1 h2
    have htp : 0 < 2 * (m : ℝ) - 1 := by linarith
    rw [← hs2]
    have : (2 * (m : ℝ) - 1) + s ^ 2 / (2 * m - 1) - 2 * s = (2 * m - 1 - s) ^ 2 / (2 * m - 1) := by
      field_simp
      ring
    have h3 : 0 ≤ (2 * (m : ℝ) - 1 - s) ^ 2 / (2 * m - 1) := by positivity
    linarith
  · exfalso
    exact h1 (by linarith)
  · have ht : s < 2 * (r : ℝ) - 1 := not_le.1 h1
    have htr : 0 < 2 * (r : ℝ) - 1 := by linarith
    have htm : 0 < 2 * (m : ℝ) - 1 := by linarith
    rw [← hs2]
    have e : ((2 * (m : ℝ) - 1) + s ^ 2 / (2 * m - 1)) - ((2 * (r : ℝ) - 1) + s ^ 2 / (2 * r - 1)) =
        (2 * (m : ℝ) - 2 * r) * ((2 * r - 1) * (2 * m - 1) - s ^ 2) /
          ((2 * r - 1) * (2 * m - 1)) := by
      field_simp
      ring
    have h3 : 0 ≤ (2 * (m : ℝ) - 2 * r) * ((2 * r - 1) * (2 * m - 1) - s ^ 2) /
        ((2 * r - 1) * (2 * m - 1)) := by
      apply div_nonneg
      · apply mul_nonneg
        · linarith
        · nlinarith
      · positivity
    linarith

lemma tendsto_factor (m : ℕ) :
    Tendsto (fun p : ℕ => (((p : ℝ) ^ (2 * m)) * ((m : ℝ) + 1)) ^ (1 / (p : ℝ))) atTop (𝓝 1) := by
  have h1 : Tendsto (fun p : ℕ => ((p : ℝ) ^ (1 / (p : ℝ)))) atTop (𝓝 1) :=
    tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun p : ℕ => (((m : ℝ) + 1)) ^ (1 / (p : ℝ))) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := ((m : ℝ) + 1))).rpow tendsto_one_div_atTop_nhds_zero_nat
      (Or.inl (by positivity))
    simpa using this
  have h3 := (h1.pow (2 * m)).mul h2
  simp only [one_pow, mul_one] at h3
  refine h3.congr (fun p => ?_)
  rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_pow_comm (by positivity)]

lemma limsup_aux {ν : ℕ → ℝ} {m : ℕ} {S : ℕ → ℕ → ℝ} {R : ℝ}
    (hS0 : ∀ p r, 0 ≤ S p r)
    (hν : ∀ p, 1 ≤ p → |ν p| ≤ (p : ℝ) ^ (2 * m) * ∑ r ∈ Finset.range (m + 1), S p r)
    (hb : ∀ r ≤ m, IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ => S p r ^ (1 / (p : ℝ))))
    (hl : ∀ r ≤ m, limsup (fun p : ℕ => S p r ^ (1 / (p : ℝ))) atTop ≤ R) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ => |ν p| ^ (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ => |ν p| ^ (1 / (p : ℝ))) atTop ≤ R := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ᶠ p : ℕ in atTop, |ν p| ^ (1 / (p : ℝ)) ≤ R + 2 * ε := by
    intro ε hε
    have ev : ∀ᶠ p : ℕ in atTop, ∀ r ∈ Finset.range (m + 1), S p r ^ (1 / (p : ℝ)) < R + ε :=
      (Filter.eventually_all_finset _).2 (fun r hr =>
        eventually_lt_of_limsup_lt
          (lt_of_le_of_lt (hl r (by simpa [Nat.lt_succ_iff] using hr)) (by linarith))
          (hb r (by simpa [Nat.lt_succ_iff] using hr)))
    have hM : 0 < R + ε := by
      obtain ⟨p, hp⟩ := (ev.and (eventually_ge_atTop 1)).exists
      have := hp.1 0 (by simp)
      have h0 : 0 ≤ S p 0 ^ (1 / (p : ℝ)) := Real.rpow_nonneg (hS0 _ _) _
      linarith
    have hf := (tendsto_factor m).eventually (gt_mem_nhds (by
      have : 0 < ε / (R + ε) := by positivity
      linarith : (1 : ℝ) < 1 + ε / (R + ε)))
    filter_upwards [ev, hf, eventually_ge_atTop 1] with p hp hfp hp1
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hpn : p ≠ 0 := by omega
    have hSle : ∀ r ∈ Finset.range (m + 1), S p r ≤ (R + ε) ^ p := by
      intro r hr
      have h1 := hp r hr
      have h0 : 0 ≤ S p r ^ (1 / (p : ℝ)) := Real.rpow_nonneg (hS0 _ _) _
      have h2 : (S p r ^ (1 / (p : ℝ))) ^ p ≤ (R + ε) ^ p := pow_le_pow_left₀ h0 h1.le p
      have h3 : (S p r ^ (1 / (p : ℝ))) ^ p = S p r := by
        rw [one_div]; exact Real.rpow_inv_natCast_pow (hS0 _ _) hpn
      rwa [h3] at h2
    have hsum : ∑ r ∈ Finset.range (m + 1), S p r ≤ ((m : ℝ) + 1) * (R + ε) ^ p := by
      refine (Finset.sum_le_sum hSle).trans ?_
      simp
    have hab : |ν p| ≤ ((p : ℝ) ^ (2 * m) * ((m : ℝ) + 1)) * (R + ε) ^ p := by
      refine (hν p hp1).trans ?_
      calc (p : ℝ) ^ (2 * m) * ∑ r ∈ Finset.range (m + 1), S p r
          ≤ (p : ℝ) ^ (2 * m) * (((m : ℝ) + 1) * (R + ε) ^ p) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = _ := by ring
    have hpow : |ν p| ^ (1 / (p : ℝ)) ≤
        (((p : ℝ) ^ (2 * m) * ((m : ℝ) + 1)) * (R + ε) ^ p) ^ (1 / (p : ℝ)) :=
      Real.rpow_le_rpow (abs_nonneg _) hab (by positivity)
    refine hpow.trans ?_
    rw [Real.mul_rpow (by positivity) (by positivity), one_div, Real.pow_rpow_inv_natCast hM.le hpn]
    have : (((p : ℝ) ^ (2 * m) * ((m : ℝ) + 1)) ^ ((p : ℝ)⁻¹)) * (R + ε) ≤
        (1 + ε / (R + ε)) * (R + ε) := by
      rw [one_div] at hfp
      exact mul_le_mul_of_nonneg_right hfp.le hM.le
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have hnn : ∀ p : ℕ, 0 ≤ |ν p| ^ (1 / (p : ℝ)) := fun p => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨isBoundedUnder_of_eventually_le (a := R + 2 * 1) (key 1 one_pos), ?_⟩
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have := key (ε / 2) (by positivity)
  have e : R + 2 * (ε / 2) = R + ε := by ring
  rw [e] at this
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hnn) this

theorem limsup_main (d m : ℕ) (hm : 2 ≤ m) (hmd : m ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) atTop ≤ rhoStair d m := by
  have hd : 2 ≤ d := by omega
  refine limsup_aux (ν := fun p => nuAdj d m ((X : ℝ[X]) ^ p)) (S := fun p r => S d p r)
    (m := m) (R := rhoStair d m) ?_ ?_ ?_ ?_
  · intro p r
    exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  · intro p hp
    exact abs_nuAdj_le d p m hp hm
  · intro r hr
    exact (limsup_sum_ncard_crit_rpow_eq_rhoStair d r hd (by omega)).1
  · intro r hr
    exact ((limsup_sum_ncard_crit_rpow_eq_rhoStair d r hd (by omega)).2).le.trans
      (rhoStair_mono hd hr)

end StrongConv.L85

namespace StrongConv

theorem limsup_abs_nuAdj_X_pow_le_rhoStair_dev (d m : ℕ) (hm : 2 ≤ m) (hmd : m ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) atTop ≤ rhoStair d m :=
  L85.limsup_main d m hm hmd

end StrongConv

end

end
end

section
open StrongConv

open Filter Polynomial


theorem solution (d m : ℕ) (hm : 2 ≤ m) (hmd : m ≤ d) :
    IsBoundedUnder (· ≤ ·) atTop (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) ∧
      limsup (fun p : ℕ => |nuAdj d m (X ^ p)| ^ (1 / (p : ℝ))) atTop ≤ rhoStair d m := by
  apply StrongConv.limsup_abs_nuAdj_X_pow_le_rhoStair_dev <;> assumption

end
