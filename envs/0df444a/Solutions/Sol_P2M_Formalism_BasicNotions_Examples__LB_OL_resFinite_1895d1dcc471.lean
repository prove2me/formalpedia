-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__LB_OL_resFinite_1895d1dcc471
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:49.397314+00:00
-- url     : https://prove2.me/submissions/e583c2d0-717e-48bd-b665-796fc0d240fb

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__LB_residue_algebraMap_7319e467ce67

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
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime] (LL : FinExt l)
namespace Formalism.BasicNotions.Examples₂.LB
theorem _root_.solution : Finite (ResidueField ↥(OL LL)) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := ↥(OL LL))
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  let f : (Fin n → ZMod l) → ResidueField ↥(OL LL) :=
    fun a => ∑ i, (((a i).val : ℕ) : ResidueField ↥(OL LL)) * residue ↥(OL LL) (s i)
  refine Finite.of_surjective f fun y => ?_
  obtain ⟨x, rfl⟩ := residue_surjective y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hx
  refine ⟨fun i => PadicInt.toZMod (c i), ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, residue_algebraMap]
end Formalism.BasicNotions.Examples₂.LB
