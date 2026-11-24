-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mCoordIdeal_yLine_1445442fc678
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:38.313971+00:00
-- url     : https://prove2.me/submissions/b03898b1-05ef-42e8-9491-e42be83f7bda

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_xL_ne_zero_6abe86b3f4b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_coe_gen_12d21276c6ec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : mCoordIdeal yLine = ⊥ := by
  let ψ : MvPolynomial Unit Ω →ₐ[Ω] L := MvPolynomial.aeval fun _ => xL 0
  let ρ : MRing (PBlk 2) →+* L := (algebraMap (MvPolynomial (Fin 2) ℚ) L).comp
    ((MvPolynomial.map (Int.castRingHom ℚ)).comp
      (rename (fun p : Σ _ : Unit, Fin 2 => p.2)).toRingHom)
  have hcomp : ψ.toRingHom.comp (mConeMap yLine).toRingHom = ρ := by
    apply MvPolynomial.ringHom_ext'
    · exact RingHom.ext_int _ _
    · rintro ⟨⟨⟩, i⟩
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        mConeMap, aeval_X, map_mul, ψ, ρ, AlgHom.coe_toRingHom, rename_X, map_X]
      fin_cases i
      · simp [yLine, xL]
      · simp only [yLine]
        rw [if_neg (by decide), MvPolynomial.aeval_C]
        show (gen : L) * xL 0 = xL 1
        rw [coe_gen, u, div_mul_cancel₀ _ (xL_ne_zero 0)]
  have hinj : Function.Injective ρ := by
    refine (IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) L).comp
      ((MvPolynomial.map_injective _ (RingHom.injective_int _)).comp (rename_injective _ ?_))
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    simp only at h
    subst h
    rfl
  ext f
  simp only [Ideal.mem_bot]
  constructor
  · intro hf
    have h1 : mConeMap yLine f = 0 := hf
    apply hinj
    rw [map_zero, ← hcomp]
    simp [h1]
  · rintro rfl
    exact zero_mem _
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
