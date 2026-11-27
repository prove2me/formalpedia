-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_IntegralFormCovolume_proof_30b87a3181e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:56:10.873372+00:00
-- url     : https://prove2.me/submissions/ea1131cb-df0f-471b-a519-2558629b267b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StIntegralFormCovolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIntegralFormCovolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open Module MeasureTheory Matrix
noncomputable section
variable (Q V K : Type*) [AddCommGroup Q] [Module ℚ Q] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype K]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace IntegralFormCovolume
theorem _root_.solution : IntegralFormCovolume.Statement Q V K := by
  classical
  intro ψ e T μ hμ hT hli hrank
  have : FiniteDimensional ℚ Q := Module.Finite.of_basis e
  have hQ : finrank ℚ Q = Fintype.card K := finrank_eq_card_basis e
  let b₀ : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hli hrank.symm
  have hb₀ : ∀ i, b₀ i = ψ (e i) := fun i => by simp [b₀]
  have hGe : (LinearMap.BilinForm.toMatrix e T).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e).1 hT
  refine ⟨μ.real (ZSpan.fundamentalDomain b₀) ^ 2 /
    |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|, ?_⟩
  intro L k hk hfg hspan _ hdual
  set M := AddSubgroup.toIntSubmodule L with hM
  have : Module.Finite ℤ M := Module.Finite.iff_fg.2 ((Submodule.fg_iff_addSubgroup_fg M).2 hfg)
  have : Module.IsTorsionFree ℤ Q := .trans_faithfulSMul ℤ ℚ Q
  have hψq : ∀ (q : ℚ) (y : Q), ψ (q • y) = (q : ℝ) • ψ y := fun q y => by
    simpa using map_ratCast_smul ψ ℚ ℝ q y

  let x₀ := Module.Free.chooseBasis ℤ M
  have hli₀ : LinearIndependent ℚ (M.subtype ∘ x₀) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1
      (x₀.linearIndependent.map' M.subtype (Submodule.ker_subtype M))
  have hspan₀ : Submodule.span ℤ (Set.range (M.subtype ∘ x₀)) = M := by
    rw [Set.range_comp, Submodule.span_image, x₀.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanq : Submodule.span ℚ (Set.range (M.subtype ∘ x₀)) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ, hspan₀]
    exact hspan
  let xq₀ : Basis _ ℚ Q := Basis.mk hli₀ hspanq.ge
  let σ := Fintype.equivOfCardEq ((finrank_eq_card_basis xq₀).symm.trans hQ)
  let x := x₀.reindex σ
  let xq := xq₀.reindex σ
  have hxq : ∀ i, xq i = (x i : Q) := fun i => by simp [xq, x, xq₀]
  have hspanx : Submodule.span ℤ (Set.range fun i => xq i) = M := by
    have : (fun i => xq i) = M.subtype ∘ x := funext hxq
    rw [this, Set.range_comp, Submodule.span_image, x.span_eq, Submodule.map_top,
      Submodule.range_subtype]

  set P := e.toMatrix xq with hP
  have hψe : ∀ y, ψ y = ∑ i, (e.repr y i : ℝ) • b₀ i := fun y => by
    calc ψ y = ψ (∑ i, e.repr y i • e i) := by rw [e.sum_repr]
      _ = _ := by rw [map_sum]; simp only [hψq, hb₀]
  have hmat : b₀.toMatrix (fun j => ψ (xq j)) = P.map (Rat.cast : ℚ → ℝ) := by
    ext i j
    rw [Basis.toMatrix_apply, hψe, b₀.repr_sum_self]
    simp [P, Basis.toMatrix_apply]
  have hdetP : b₀.det (fun j => ψ (xq j)) = (P.det : ℝ) := by
    rw [Basis.det_apply, hmat]
    simpa using (RingHom.map_det (Rat.castHom ℝ) P).symm
  have hP0 : P.det ≠ 0 := by
    rw [hP, ← Basis.det_apply]
    exact (e.isUnit_det xq).ne_zero
  have hw : LinearIndependent ℝ (fun j => ψ (xq j)) :=
    ((Basis.is_basis_iff_det b₀).2 (by rw [hdetP]; exact isUnit_iff_ne_zero.2 (by exact_mod_cast hP0))).1
  let bx : Basis K ℝ V := basisOfLinearIndependentOfCardEqFinrank' _ hw hrank.symm
  have hL : AddSubgroup.toIntSubmodule (L.map ψ) = Submodule.span ℤ (Set.range bx) := by
    change M.map ψ.toIntLinearMap = _
    rw [← hspanx, Submodule.map_span, ← Set.range_comp]
    congr 1
    simp [bx, Function.comp_def]

  have hPk : P.det ^ 2 * |(LinearMap.BilinForm.toMatrix e T).det| ≤ |(k : ℚ)| ^ Fintype.card K := by
    have hG : (LinearMap.BilinForm.toMatrix xq T).det =
        P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det := by
      rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix e xq T, det_mul, det_mul, det_transpose]
      ring
    set d := T.dualBasis hT xq
    have hd : ∀ i j, T (d i) (xq j) = if j = i then 1 else 0 :=
      LinearMap.BilinForm.apply_dualBasis_left hT xq
    have hc : ∀ i, ∃ c : K → ℤ, ∑ j, c j • xq j = k • d i := by
      intro i
      have hmem : k • d i ∈ L := hdual (d i) fun y hy => by
        have hy' : y ∈ Submodule.span ℤ (Set.range fun j => xq j) := by rw [hspanx]; exact hy
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
        exact ⟨c i, by simp [map_sum, hd]⟩
      have hmem' : k • d i ∈ Submodule.span ℤ (Set.range fun j => xq j) := by
        rw [hspanx]; exact hmem
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem'
    choose c₀ hc using hc
    set c : Matrix K K ℤ := Matrix.of c₀ with hcdef
    have hcG : c.map (Int.cast : ℤ → ℚ) * LinearMap.BilinForm.toMatrix xq T = (k : ℚ) • 1 := by
      ext i l
      have h1 := congrArg (fun y => T y (xq l)) (hc i)
      simp [hd] at h1
      rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
      simp only [Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply, hcdef, Matrix.of_apply]
      simpa [zsmul_eq_mul, eq_comm] using h1
    have hdet := congrArg Matrix.det hcG
    rw [det_mul, det_smul, det_one, mul_one, hG] at hdet
    have hcd : (c.map (Int.cast : ℤ → ℚ)).det = (c.det : ℚ) := by
      simpa using (RingHom.map_det (Int.castRingHom ℚ) c).symm
    rw [hcd] at hdet
    have hc0 : c.det ≠ 0 := by
      rintro h0
      rw [h0, Int.cast_zero, zero_mul] at hdet
      exact pow_ne_zero _ (Int.cast_ne_zero.2 hk) hdet.symm
    have h1 : (1 : ℚ) ≤ |(c.det : ℚ)| := by exact_mod_cast Int.one_le_abs hc0
    calc P.det ^ 2 * |(LinearMap.BilinForm.toMatrix e T).det|
        = |P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det| := by
          rw [abs_mul, abs_pow, sq_abs]
      _ ≤ |(c.det : ℚ)| * |P.det ^ 2 * (LinearMap.BilinForm.toMatrix e T).det| :=
          le_mul_of_one_le_left (abs_nonneg _) h1
      _ = |(k : ℚ)| ^ Fintype.card K := by rw [← abs_mul, hdet, abs_pow]
  have hPkR : (P.det : ℝ) ^ 2 * |((LinearMap.BilinForm.toMatrix e T).det : ℝ)| ≤
      |(k : ℝ)| ^ Fintype.card K := by exact_mod_cast hPk

  rw [hL]
  refine ⟨inferInstance, inferInstance, ?_⟩
  have := hμ
  let bZ : Basis K ℤ (Submodule.span ℤ (Set.range bx)) :=
    Basis.span (bx.linearIndependent.restrict_scalars' ℤ)
  have hcoe : ((↑) ∘ bZ : K → V) = fun j => ψ (xq j) := funext fun i => by
    simp [bZ, Basis.span_apply, bx]
  rw [ZLattice.covolume_eq_det_mul_measureReal _ μ bZ b₀, hcoe, hdetP, mul_pow, sq_abs,
    div_mul_eq_mul_div, le_div_iff₀ (abs_pos.2 (by exact_mod_cast hGe))]
  calc (P.det : ℝ) ^ 2 * μ.real (ZSpan.fundamentalDomain b₀) ^ 2 *
        |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|
      = μ.real (ZSpan.fundamentalDomain b₀) ^ 2 *
        ((P.det : ℝ) ^ 2 * |((LinearMap.BilinForm.toMatrix e T).det : ℝ)|) := by ring
    _ ≤ μ.real (ZSpan.fundamentalDomain b₀) ^ 2 * |(k : ℝ)| ^ Fintype.card K :=
        mul_le_mul_of_nonneg_left hPkR (sq_nonneg _)
end IntegralFormCovolume
end GroundTheory.Heights₂.Heights.FiniteCovolume
