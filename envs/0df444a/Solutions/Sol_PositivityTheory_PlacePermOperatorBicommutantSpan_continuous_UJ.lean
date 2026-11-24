-- Prove2me | solution 1 for PositivityTheory.PlacePermOperatorBicommutantSpan.continuous_UJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:49.063514+00:00
-- url     : https://prove2.me/submissions/6e85857d-6ead-4451-bce3-8373b271ddec

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_Development_WeilBound_CoreStatements_ThetaDilations_ParAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open PositivityTheory PositivityTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}
namespace PositivityTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution {n : ℕ} [TopologicalSpace K] [IsTopologicalRing K] {s : K →+* K} (hs : Continuous s)
    {J Ji : Matrix (Fin n) (Fin n) K} (hJ : Ji * J = 1) :
    Topology.IsInducing fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have h1 : Continuous fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_val.comp continuous_subtype_val
  have h2 : Continuous fun g : Matrix (Fin n) (Fin n) K => (g, MulOpposite.op (Ji * cT s g * J)) :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul (continuous_id.matrix_map hs).matrix_transpose).matrix_mul continuous_const))
  refine Topology.IsInducing.of_comp h1 h2 ?_
  have h3 := (Units.isInducing_embedProduct (M := Matrix (Fin n) (Fin n) K)).comp
    (Topology.IsInducing.subtypeVal (t := (UJ s J : Set (GL (Fin n) K))))
  have e : ((fun g : Matrix (Fin n) (Fin n) K => (g, MulOpposite.op (Ji * cT s g * J))) ∘
      fun g : UJ s J => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) =
      fun g : UJ s J => Units.embedProduct _ (g : GL (Fin n) K) := by
    funext g
    have : g = mkU s hJ _ g.2 := Subtype.ext (Units.ext rfl)
    conv_rhs => rw [this]
    rfl
  rw [e]
  exact h3
end PositivityTheory.PlacePermOperatorBicommutantSpan
