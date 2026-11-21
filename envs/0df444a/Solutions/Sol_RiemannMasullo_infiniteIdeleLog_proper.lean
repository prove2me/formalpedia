-- Prove2me | solution 1 for RiemannMasullo.infiniteIdeleLog_proper
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T00:33:47.904249+00:00
-- url     : https://prove2.me/submissions/d98085aa-97b1-4c4e-9bfb-3eb5d188a291

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppA_AlgebraicNT/Sec2b.lean#L121-L122
import Mathlib
import Theorems.Thm_RiemannMasullo_infiniteIdeleLog_continuous
import Definitions.Def_RiemannMasullo_InfiniteIdeleLogNorm
open RiemannMasullo
open Function NumberField InfinitePlace.Completion Topology
open scoped Classical NNReal
variable (F : Type*) [Field F] [NumberField F]
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

theorem solution : IsProperMap (infiniteIdeleLog F) := by
  classical
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨infiniteIdeleLog_continuous F, ?_⟩
  intro K hK
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  let r (v : InfinitePlace F) := Real.exp (C / v.mult)
  let S : Set (InfiniteAdeleRing F) := Set.univ.pi fun v ↦ Metric.closedBall 0 (r v)
  have hs : IsCompact S := by
    apply isCompact_univ_pi
    intro v
    by_cases hv : v.IsReal
    · let e := isometryEquivRealOfIsReal hv
      rw [← e.isometry.preimage_closedBall (0 : v.Completion)]
      exact e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
    · let e := isometryEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.mp hv)
      rw [← e.isometry.preimage_closedBall (0 : v.Completion)]
      exact e.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  haveI : T1Space (InfiniteAdeleRing F) := inferInstanceAs (T1Space ((v : InfinitePlace F) → v.Completion))
  let T := (Units.embedProduct (InfiniteAdeleRing F)) ⁻¹' (S ×ˢ (MulOpposite.op '' S))
  have ht : IsCompact T := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hs.prod (hs.image MulOpposite.continuous_op))
  apply ht.of_isClosed_subset (hK.isClosed.preimage (infiniteIdeleLog_continuous F))
  intro g hg
  have hb (v : InfinitePlace F) : |(infiniteIdeleLog F g) v| ≤ C :=
    (norm_le_pi_norm _ v).trans (hC _ hg)
  have hne (v : InfinitePlace F) : g.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g).ne_zero
  have hbounds (v : InfinitePlace F) :
      ‖g.val v‖ ≤ r v ∧ ‖(g.val v)⁻¹‖ ≤ r v := by
    have hm : 0 < (v.mult : ℝ) := Nat.cast_pos.mpr InfinitePlace.mult_pos
    obtain ⟨hl, hu⟩ := abs_le.mp (hb v)
    change -C ≤ (v.mult : ℝ) * Real.log ‖g.val v‖ at hl
    change (v.mult : ℝ) * Real.log ‖g.val v‖ ≤ C at hu
    have hp : 0 < ‖g.val v‖ := norm_pos_iff.mpr (hne v)
    constructor
    · exact (Real.log_le_iff_le_exp hp).mp ((le_div_iff₀ hm).mpr (by linarith))
    · rw [norm_inv]
      apply (Real.log_le_iff_le_exp (inv_pos.mpr hp)).mp
      rw [Real.log_inv]
      apply (le_div_iff₀ hm).mpr
      linarith
  refine ⟨fun v _ ↦ ?_, ⟨(↑g⁻¹ : InfiniteAdeleRing F), fun v _ ↦ ?_, rfl⟩⟩
  · change dist (g.val v) 0 ≤ r v
    rw [dist_zero_right]
    exact (hbounds v).1
  · have hi := (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g).val_inv_eq_inv_val
    change dist ((↑g⁻¹ : InfiniteAdeleRing F) v) 0 ≤ r v
    rw [dist_zero_right]
    exact (le_of_eq (congrArg norm hi)).trans (hbounds v).2
