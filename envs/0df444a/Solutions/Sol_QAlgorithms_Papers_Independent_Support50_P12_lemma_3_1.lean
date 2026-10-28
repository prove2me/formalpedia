-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P12.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:05:59.863642+00:00
-- url     : https://prove2.me/submissions/d11c059a-4e58-4644-a4a9-15c0efcf7ccc

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12
noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]


section S169I
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma S169I_aeval_mem (A : Alg I) (S : Mat I) (hS : S ∈ A) (p : Polynomial ℝ) :
    Polynomial.aeval S p ∈ A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact A.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, IsScalarTower.algebraMap_apply ℝ ℂ (Mat I)]
    exact A.mul_mem (A.algebraMap_mem _) (A.pow_mem hS n)

lemma S169I_cfc_mem (A : Alg I) (S : Mat I) (hS : S ∈ A) (hSa : IsSelfAdjoint S) (f : ℝ → ℝ) :
    cfc f S ∈ A := by
  have hfin := Matrix.finite_real_spectrum (A := S)
  set T := hfin.toFinset
  let p : Polynomial ℝ := Lagrange.interpolate T id f
  have hp : ∀ x ∈ spectrum ℝ S, p.eval x = f x := by
    intro x hx
    exact Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) (i := x)
      (Set.injOn_id _) (hfin.mem_toFinset.mpr hx)
  have h1 : cfc f S = cfc p.eval S := cfc_congr fun x hx => (hp x hx).symm
  rw [h1, cfc_polynomial p S]
  exact S169I_aeval_mem A S hS p

lemma S169I_supp_eq (S : Mat I) :
    supp S = cfc (fun x : ℝ => if x = 0 then (0:ℝ) else 1) S := by
  unfold supp supportPower
  congr 1; funext x; split_ifs <;> simp [Real.rpow_zero]

lemma S169I_P_props (S : Mat I) (hS : S.PosSemidef) :
    IsSelfAdjoint (supp S) ∧ supp S * supp S = supp S ∧ S * supp S = S ∧
      ∃ lam : ℝ, 0 ≤ lam ∧ supp S ≤ (lam : ℂ) • S := by
  have hSa : IsSelfAdjoint S := hS.1
  have hfin := Matrix.finite_real_spectrum (A := S)
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ S) := fun f => hfin.continuousOn f
  set g : ℝ → ℝ := fun x => if x = 0 then (0:ℝ) else 1
  rw [S169I_supp_eq]
  refine ⟨cfc_predicate _ _, ?_, ?_, ?_⟩
  · rw [← cfc_mul g g S (hc g) (hc g)]
    exact cfc_congr fun x _ => by simp only [g, Pi.mul_apply]; split_ifs <;> simp
  · have hm := cfc_mul (fun x : ℝ => x) g S (hc _) (hc g)
    rw [cfc_id' (R := ℝ) (a := S)] at hm
    rw [← hm]
    conv_rhs => rw [← cfc_id' (R := ℝ) (a := S)]
    exact cfc_congr fun x _ => by simp only [g]; split_ifs with h <;> simp [h]
  · have hnn : ∀ x ∈ spectrum ℝ S, 0 ≤ x := fun x hx =>
      spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hS) hx
    set lam : ℝ := ∑ x ∈ hfin.toFinset, x⁻¹
    have hlam : ∀ x ∈ spectrum ℝ S, x⁻¹ ≤ lam := fun x hx =>
      Finset.single_le_sum (f := fun x => x⁻¹) (fun y hy => inv_nonneg.mpr
        (hnn y (hfin.mem_toFinset.mp hy))) (hfin.mem_toFinset.mpr hx)
    have hlam0 : 0 ≤ lam := Finset.sum_nonneg fun y hy => inv_nonneg.mpr (hnn y (hfin.mem_toFinset.mp hy))
    refine ⟨lam, hlam0, ?_⟩
    have e : ((lam : ℂ)) • S = cfc (fun x => lam * x) S := by
      rw [cfc_const_mul_id lam S, ← Complex.coe_smul]
    rw [e]
    apply cfc_mono (hf := hc g) (hg := hc _)
    intro x hx
    simp only [g]
    split_ifs with h0
    · rw [h0, mul_zero]
    · have hxpos : 0 < x := lt_of_le_of_ne (hnn x hx) (Ne.symm h0)
      have := hlam x hx
      rw [inv_le_iff_one_le_mul₀ hxpos] at this
      linarith [mul_comm x lam]

end S169I

section S169L
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma S169L_ker_supp (M : Mat I) (hM : M.PosSemidef) (v : I → ℂ) :
    M *ᵥ v = 0 ↔ supp M *ᵥ v = 0 := by
  obtain ⟨hPsa, hPP, hSP, lam, hlam0, hPle⟩ := S169I_P_props M hM
  constructor
  · intro hv
    have hPpsd : (supp M).PosSemidef := by
      have hPH : (supp M)ᴴ = supp M := hPsa
      have : supp M = (supp M)ᴴ * supp M := by rw [hPH, hPP]
      rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
    have h1 := (Matrix.le_iff.mp hPle).dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, dotProduct_sub, dotProduct_zero,
      zero_sub] at h1
    have h2 := hPpsd.dotProduct_mulVec_nonneg v
    exact (hPpsd.dotProduct_mulVec_zero_iff v).mp (le_antisymm (neg_nonneg.mp h1) h2)
  · intro hv
    rw [← hSP, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

lemma S169L_idem_eq (P Q : Mat I) (hP : Pᴴ = P) (hQ : Qᴴ = Q) (hPP : P * P = P) (hQQ : Q * Q = Q)
    (hk : ∀ v, P *ᵥ v = 0 ↔ Q *ᵥ v = 0) : P = Q := by
  have key : ∀ P Q : Mat I, Pᴴ = P → Qᴴ = Q → P * P = P → Q * Q = Q →
      (∀ v, Q *ᵥ v = 0 → P *ᵥ v = 0) → Q * P = P := by
    intro P Q hP hQ hPP hQQ hk
    have h1 : P * (P - Q * P) = 0 := by
      ext i j
      have hw : Q *ᵥ ((P - Q * P) *ᵥ Pi.single j 1) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_sub, ← Matrix.mul_assoc, hQQ, sub_self, Matrix.zero_mulVec]
      have := congrFun (hk _ hw) i
      rw [Matrix.mulVec_mulVec] at this
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
    have h2 : (P - Q * P)ᴴ * (P - Q * P) = 0 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hP, hQ, Matrix.sub_mul, h1, zero_sub,
        Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc Q Q, hQQ, sub_self, Matrix.mul_zero, neg_zero]
    have := Matrix.conjTranspose_mul_self_eq_zero.mp h2
    exact (sub_eq_zero.mp this).symm
  have e1 := key P Q hP hQ hPP hQQ fun v hv => (hk v).mpr hv
  have e2 := key Q P hQ hP hQQ hPP fun v hv => (hk v).mp hv
  calc P = Pᴴ := hP.symm
    _ = (Q * P)ᴴ := by rw [e1]
    _ = P * Q := by rw [Matrix.conjTranspose_mul, hP, hQ]
    _ = Q := e2

lemma S169L_supp_eq (M N : Mat I) (hM : M.PosSemidef) (hN : N.PosSemidef)
    (hk : ∀ v, M *ᵥ v = 0 ↔ N *ᵥ v = 0) : supp M = supp N := by
  obtain ⟨hP1, hPP1, -, -⟩ := S169I_P_props M hM
  obtain ⟨hP2, hPP2, -, -⟩ := S169I_P_props N hN
  exact S169L_idem_eq _ _ hP1 hP2 hPP1 hPP2 fun v =>
    (S169L_ker_supp M hM v).symm.trans ((hk v).trans (S169L_ker_supp N hN v))

lemma S169L_dom (A : Alg I) (X Y : Mat I) (hXp : X.PosSemidef) (hYp : Y.PosSemidef)
    (h : supp X = supp Y) : ∃ c : ℝ, 0 ≤ c ∧ X ≤ (c : ℂ) • Y := by
  obtain ⟨hPsa, hPP, hSP, -, -, -⟩ := S169I_P_props X hXp
  obtain ⟨-, -, -, lam, hlam0, hPle⟩ := S169I_P_props Y hYp
  set r : ℝ := ‖X‖
  refine ⟨r * lam, mul_nonneg (norm_nonneg _) hlam0, ?_⟩
  have hhi : X ≤ algebraMap ℝ (Mat I) r := IsSelfAdjoint.le_algebraMap_norm_self hXp.1
  have halg : algebraMap ℝ (Mat I) r = ((r : ℂ)) • (1 : Mat I) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [halg] at hhi
  have c2 := star_left_conjugate_le_conjugate hhi (supp X)
  have hPs : star (supp X) = supp X := hPsa
  rw [hPs, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP] at c2
  have hXP : X * supp X = X := hSP
  have hPX : supp X * X = X := by
    have := congrArg Matrix.conjTranspose hXP
    rwa [Matrix.conjTranspose_mul, show (supp X)ᴴ = supp X from hPsa, hXp.1.eq] at this
  rw [hPX, hXP, h] at c2
  calc X ≤ ((r : ℂ)) • supp Y := c2
    _ ≤ ((r : ℂ)) • (((lam : ℂ)) • Y) := by
        rw [Matrix.le_iff, ← smul_sub]
        exact (Matrix.le_iff.mp hPle).smul (by exact_mod_cast norm_nonneg X)
    _ = (((r * lam : ℝ)) : ℂ) • Y := by rw [smul_smul]; push_cast; rfl

lemma S169L_ker_map (A : Alg I) (Phi : MatrixMap I J) (hp : PositiveOnConcreteAlgebra A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef)
    (h : supp X = supp Y) (v : J → ℂ) (hv : Phi Y *ᵥ v = 0) : Phi X *ᵥ v = 0 := by
  obtain ⟨c, hc, hle⟩ := S169L_dom A X Y hXp hYp h
  have hpsd := hp _ (A.sub_mem (A.smul_mem hY _) hX) (Matrix.le_iff.mp hle)
  have h1 := hpsd.dotProduct_mulVec_nonneg v
  rw [map_sub, map_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, dotProduct_sub,
    dotProduct_zero, zero_sub] at h1
  have hXp' := hp X hX hXp
  exact (hXp'.dotProduct_mulVec_zero_iff v).mp
    (le_antisymm (neg_nonneg.mp h1) (hXp'.dotProduct_mulVec_nonneg v))

theorem S169L_main [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) :
    (supp X = supp Y → supp (Phi X) = supp (Phi Y)) ∧
    supp (Phi Y) = supp (Phi (supp Y)) := by
  have part1 : ∀ X Y : Mat I, X ∈ A → Y ∈ A → X.PosSemidef → Y.PosSemidef →
      supp X = supp Y → supp (Phi X) = supp (Phi Y) := by
    intro X Y hX hY hXp hYp h
    exact S169L_supp_eq _ _ (hp X hX hXp) (hp Y hY hYp) fun v =>
      ⟨S169L_ker_map A Phi hp Y X hY hX hYp hXp h.symm v,
        S169L_ker_map A Phi hp X Y hX hY hXp hYp h v⟩
  refine ⟨part1 X Y hX hY hXp hYp, ?_⟩
  obtain ⟨hPsa, hPP, -, -⟩ := S169I_P_props Y hYp
  have hPA : supp Y ∈ A := by rw [S169I_supp_eq]; exact S169I_cfc_mem A _ hY hYp.1 _
  have hPpsd : (supp Y).PosSemidef := by
    have hPH : (supp Y)ᴴ = supp Y := hPsa
    have : supp Y = (supp Y)ᴴ * supp Y := by rw [hPH, hPP]
    rw [this]; exact Matrix.posSemidef_conjTranspose_mul_self _
  have hss : supp (supp Y) = supp Y :=
    S169L_supp_eq _ _ hPpsd hYp fun v => (S169L_ker_supp Y hYp v).symm
  exact (part1 _ _ hPA hY hPpsd hYp hss).symm

end S169L

end QAlgorithms.Papers.Independent.Support50.P12

end

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Support50.P12
open QAlgorithms.Papers.Independent.Information100.P60 (Mat)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

theorem solution {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Nonempty I] [Nonempty J] (A : Alg I) (B : Alg J)
    (Phi : MatrixMap I J) (hc : AlgebraExtension A B Phi) (hp : PositiveOnConcreteAlgebra A Phi)
    (X Y : Mat I) (hX : X ∈ A) (hY : Y ∈ A) (hXp : X.PosSemidef) (hYp : Y.PosSemidef) :
    (supp X = supp Y → supp (Phi X) = supp (Phi Y)) ∧
    supp (Phi Y) = supp (Phi (supp Y)) :=
  S169L_main A B Phi hc hp X Y hX hY hXp hYp
