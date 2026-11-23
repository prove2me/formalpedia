-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_denseRange_emb_e16ca7438e57
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:37.155903+00:00
-- url     : https://prove2.me/submissions/ee88675b-2914-4a2a-bb83-c47f6eb4b657

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Pointwise
variable (l : ℕ) [hl : Fact l.Prime]
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) :
    DenseRange j := by
  have : CharZero Ω := (RingHom.charZero_iff j.injective).mpr inferInstance
  rw [Metric.denseRange_iff]
  intro a ε hε
  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  set f := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fa0 : aeval a f = 0 := minpoly.aeval _ _
  have hn : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hε' : (ε / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  have hd : DenseRange (algebraMap ℚ ℚ_[l]) := by
    have := Padic.denseRange_ratCast l
    convert this using 1
    funext q
    exact eq_ratCast _ q
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd fmon hε'
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε' fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < ε := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos hε (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [hn]
    · positivity
  have e : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l)) =
      (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, e, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨c, -, rfl⟩ := hb
  exact ⟨c, by rw [dist_eq_norm]; exact hab⟩
end Formalism.BasicNotions.Examples₂.LB
