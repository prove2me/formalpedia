-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P19.commutingReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T13:41:36.390553+00:00
-- url     : https://prove2.me/submissions/fec9f5ab-8ff3-4c73-9560-f3dc35a31ff0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P19

noncomputable section
open scoped Matrix

namespace X7cr

variable {I : Type} [Fintype I] [DecidableEq I]

lemma conj_herm (U : Matrix.unitaryGroup I ℂ) (d : I → ℝ) :
    IsSelfAdjoint ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ) := by
  have hD : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.diagonal_conjTranspose]; congr 1; funext i; simp
  exact Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix I I ℂ) hD

lemma spec_sub (U : Matrix.unitaryGroup I ℂ) (d : I → ℝ) (x : ℝ)
    (hx : x ∈ spectrum ℝ ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ)) :
    ∃ i, d i = x := by
  have e : ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ) =
      Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U (Matrix.diagonal (fun i => (d i : ℂ))) := rfl
  rw [e, AlgEquiv.spectrum_eq] at hx
  have h2 : algebraMap ℝ ℂ x ∈ spectrum ℂ (Matrix.diagonal (fun i => (d i : ℂ))) :=
    (spectrum.algebraMap_mem_iff ℂ).mpr hx
  rw [spectrum_diagonal] at h2
  obtain ⟨i, hi⟩ := h2
  exact ⟨i, by simpa using hi⟩

lemma cfc_conj (U : Matrix.unitaryGroup I ℂ) (d : I → ℝ) (f : ℝ → ℝ) :
    cfc f ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ) =
      (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (f (d i) : ℂ)) * (U : Matrix I I ℂ)ᴴ := by
  set M := (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ
  have hM : IsSelfAdjoint M := conj_herm U d
  let s : Finset ℝ := Finset.univ.image d
  let P : Polynomial ℝ := Lagrange.interpolate s id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _)
      (Finset.mem_image_of_mem d (Finset.mem_univ i))
    simpa [P] using this
  have h1 : cfc f M = cfc (fun x => P.eval x) M := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := spec_sub U d x hx
    exact (hP i).symm
  rw [h1, cfc_polynomial P M hM]
  have e : M = Unitary.conjStarAlgAut ℝ (Matrix I I ℂ) U (Matrix.diagonal (fun i => (d i : ℂ))) := rfl
  rw [e, Polynomial.aeval_algHom_apply, Unitary.conjStarAlgAut_apply]
  congr 2
  have : Matrix.diagonal (fun i => (d i : ℂ)) = Matrix.diagonalAlgHom ℝ (fun i => (d i : ℂ)) := rfl
  rw [this, Polynomial.aeval_algHom_apply]
  simp only [Matrix.diagonalAlgHom_apply]
  congr 1
  funext i
  rw [Polynomial.aeval_pi_apply]   -- may need adjusting
  rw [← hP i]
  have := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (d i) P
  simpa using this

end X7cr

end


noncomputable section
open scoped Matrix

namespace X7cr

variable {I : Type} [Fintype I] [DecidableEq I]

abbrev cj (U : Matrix.unitaryGroup I ℂ) (d : I → ℝ) : Matrix I I ℂ :=
  (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (d i : ℂ)) * (U : Matrix I I ℂ)ᴴ

lemma cj_mul (U : Matrix.unitaryGroup I ℂ) (a b : I → ℝ) :
    cj U a * cj U b = cj U (fun i => a i * b i) := by
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self U
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [cj]
  calc (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (a i : ℂ)) * (U : Matrix I I ℂ)ᴴ *
        ((U : Matrix I I ℂ) * Matrix.diagonal (fun i => (b i : ℂ)) * (U : Matrix I I ℂ)ᴴ)
      = (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (a i : ℂ)) * ((U : Matrix I I ℂ)ᴴ *
        (U : Matrix I I ℂ)) * Matrix.diagonal (fun i => (b i : ℂ)) * (U : Matrix I I ℂ)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.mul_assoc (U : Matrix I I ℂ), Matrix.diagonal_mul_diagonal]
        congr 3; funext i; push_cast; ring

lemma cj_tr (U : Matrix.unitaryGroup I ℂ) (a : I → ℝ) : (cj U a).trace.re = ∑ i, a i := by
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self U
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [cj]
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
  simp

lemma cj_cfc (U : Matrix.unitaryGroup I ℂ) (a : I → ℝ) (f : ℝ → ℝ) :
    cfc f (cj U a) = cj U (fun i => f (a i)) := cfc_conj U a f

lemma cj_ker (U : Matrix.unitaryGroup I ℂ) (a : I → ℝ) (v : I → ℂ) :
    (cj U a).mulVecLin v = 0 ↔ ∀ i, a i * ((U : Matrix I I ℂ)ᴴ *ᵥ v) i = 0 := by
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := by
    have := Matrix.UnitaryGroup.star_mul_self U
    simpa [Matrix.star_eq_conjTranspose] using this
  simp only [Matrix.mulVecLin_apply, cj]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h i
    have h2 := congrArg (fun w => (U : Matrix I I ℂ)ᴴ *ᵥ w) h
    rw [Matrix.mulVec_mulVec (M := (U : Matrix I I ℂ)ᴴ) (N := (U : Matrix I I ℂ)), hU,
      Matrix.one_mulVec, Matrix.mulVec_zero] at h2
    have h3 := congrFun h2 i
    rw [Matrix.mulVec_diagonal] at h3
    exact_mod_cast h3
  · intro h
    have : Matrix.diagonal (fun i => (a i : ℂ)) *ᵥ ((U : Matrix I I ℂ)ᴴ *ᵥ v) = 0 := by
      funext i; rw [Matrix.mulVec_diagonal]; exact h i
    rw [this, Matrix.mulVec_zero]

lemma cj_supp (U : Matrix.unitaryGroup I ℂ) (p q : I → ℝ) :
    LinearMap.ker (cj U q).mulVecLin ≤ LinearMap.ker (cj U p).mulVecLin ↔ ∀ i, q i = 0 → p i = 0 := by
  constructor
  · intro h i hi
    let v : I → ℂ := (U : Matrix I I ℂ) *ᵥ Pi.single i 1
    have hv : (U : Matrix I I ℂ)ᴴ *ᵥ v = Pi.single i 1 := by
      simp only [v, Matrix.mulVec_mulVec]
      have : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 := by
        have := Matrix.UnitaryGroup.star_mul_self U
        simpa [Matrix.star_eq_conjTranspose] using this
      rw [this, Matrix.one_mulVec]
    have h1 : v ∈ LinearMap.ker (cj U q).mulVecLin := by
      rw [LinearMap.mem_ker, cj_ker, hv]
      intro j; by_cases hj : j = i
      · subst hj; simp [hi]
      · simp [Pi.single_apply, hj]
    have h2 := h h1
    rw [LinearMap.mem_ker, cj_ker, hv] at h2
    simpa using h2 i
  · intro h v hv
    rw [LinearMap.mem_ker, cj_ker] at hv ⊢
    intro i
    rcases mul_eq_zero.mp (hv i) with h0 | h0
    · rw [h i (by exact_mod_cast h0)]; simp
    · rw [h0, mul_zero]

end X7cr

end


noncomputable section
open scoped Matrix

namespace X7cr

variable {I : Type} [Fintype I] [DecidableEq I]

open QAlgorithms.Papers.Independent.Dependency50.P35 (elog)
open QAlgorithms.Papers.Independent.Dependency50.P09 (logExt)

lemma logExt_eq (x : ℝ) (hx : 0 ≤ x) : logExt (x : EReal) = elog x := by
  unfold logExt elog
  rcases hx.lt_or_eq with h | h
  · rw [if_neg (EReal.coe_ne_top x), if_neg (by exact_mod_cast not_le.mpr h), if_pos h]; rfl
  · subst h; simp

lemma sand_term (a : ℝ) (ha : 1 < a) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : q = 0 → p = 0) :
    (fun x : ℝ => if x = 0 then 0 else Real.rpow x a)
      ((fun x : ℝ => if x = 0 then 0 else Real.rpow x ((1 - a) / (2 * a))) q * p *
        (fun x : ℝ => if x = 0 then 0 else Real.rpow x ((1 - a) / (2 * a))) q) =
      if p = 0 then 0 else p ^ a * q ^ (1 - a) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hq0 : q ≠ 0 := fun h => hp0 (hs h)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  simp only [hq0, hp0, if_false]
  have e : q ^ ((1 - a) / (2 * a)) * p * q ^ ((1 - a) / (2 * a)) = q ^ ((1 - a) / a) * p := by
    rw [mul_comm _ p, mul_assoc, ← Real.rpow_add hqp]; ring_nf
  change (if q ^ ((1 - a) / (2 * a)) * p * q ^ ((1 - a) / (2 * a)) = 0 then 0 else
      (q ^ ((1 - a) / (2 * a)) * p * q ^ ((1 - a) / (2 * a))) ^ a) = _
  rw [e]
  have hpos : 0 < q ^ ((1 - a) / a) * p := mul_pos (Real.rpow_pos_of_pos hqp _) hpp
  rw [if_neg hpos.ne', Real.mul_rpow (Real.rpow_nonneg hq _) hp, ← Real.rpow_mul hq]
  have : (1 - a) / a * a = 1 - a := by field_simp
  rw [this, mul_comm]

lemma petz_term (a : ℝ) (p q : ℝ) (hs : q = 0 → p = 0) :
    (fun x : ℝ => if x = 0 then 0 else Real.rpow x a) p *
      (fun x : ℝ => if x = 0 then 0 else Real.rpow x (1 - a)) q =
      if p = 0 then 0 else p ^ a * q ^ (1 - a) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hq0 : q ≠ 0 := fun h => hp0 (hs h)
  simp only [hq0, hp0, if_false]; rfl

end X7cr

end

section
open scoped Matrix ComplexOrder ComplexConjugate ENNReal
open Filter Topology
open QAlgorithms.Papers.Independent.Support50.P19
attribute [local instance] Classical.propDecidable Classical.decEq
open QAlgorithms.Papers.Independent.Dependency50.P35
  (tr Dominates spectralPower elog elogNN rawTrace cq)
open QAlgorithms.Papers.Independent.Dependency50.P09 (sandwichedD petzD relativeD)
variable {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq L]

theorem solution [Nonempty I] (a : ℝ) (ha : 1 < a) (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (U : Matrix.unitaryGroup I ℂ) :
    let A := (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (p i : ℂ)) * (U : Matrix I I ℂ)ᴴ
    let B := (U : Matrix I I ℂ) * Matrix.diagonal (fun i => (q i : ℂ)) * (U : Matrix I I ℂ)ᴴ
    sandwichedD a A B = petzD a A B ∧ petzD a A B = classicalRenyiBits a p q := by
  intro A B
  change sandwichedD a (X7cr.cj U p) (X7cr.cj U q) = petzD a (X7cr.cj U p) (X7cr.cj U q) ∧
    petzD a (X7cr.cj U p) (X7cr.cj U q) = classicalRenyiBits a p q
  have hsupp := X7cr.cj_supp U p q
  unfold sandwichedD petzD classicalRenyiBits
  unfold QAlgorithms.Papers.Independent.Information100.P71.SupportIncluded
  rw [hsupp]
  by_cases hs : ∀ i, q i = 0 → p i = 0
  swap
  · simp [hs, ha]
  simp only [hs, not_true, and_false, if_false, if_true]
  unfold QAlgorithms.Papers.Independent.Information100.P71.supportPower
  simp only [X7cr.cj_cfc, X7cr.cj_mul, X7cr.cj_tr]
  have h1 : ∀ i, (fun x : ℝ => if x = 0 then 0 else Real.rpow x a)
      ((fun x : ℝ => if x = 0 then 0 else Real.rpow x ((1 - a) / (2 * a))) (q i) * p i *
        (fun x : ℝ => if x = 0 then 0 else Real.rpow x ((1 - a) / (2 * a))) (q i)) =
      if p i = 0 then 0 else p i ^ a * q i ^ (1 - a) :=
    fun i => X7cr.sand_term a ha (p i) (q i) (hp i) (hq i) (hs i)
  have h2 : ∀ i, (fun x : ℝ => if x = 0 then 0 else Real.rpow x a) (p i) *
      (fun x : ℝ => if x = 0 then 0 else Real.rpow x (1 - a)) (q i) =
      if p i = 0 then 0 else p i ^ a * q i ^ (1 - a) :=
    fun i => X7cr.petz_term a (p i) (q i) (hs i)
  simp only [h1, h2]
  have hnn : 0 ≤ ∑ i, (if p i = 0 then 0 else p i ^ a * q i ^ (1 - a)) := by
    apply Finset.sum_nonneg; intro i _
    split_ifs
    · exact le_refl _
    · exact mul_nonneg (Real.rpow_nonneg (hp i) _) (Real.rpow_nonneg (hq i) _)
  rw [X7cr.logExt_eq _ hnn]
  refine ⟨?_, ?_⟩
  · first | trivial | rfl
  · rw [if_neg (fun h => h.2 hs), if_pos hs]

end
