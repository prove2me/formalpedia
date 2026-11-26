-- Prove2me | solution 1 for SP4Mission.whitehead_contractible
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @loader3229
-- created : 2026-11-26T10:41:32.486957+00:00
-- url     : https://prove2.me/submissions/55963057-7317-401d-a073-443208896957
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.CWComplex.Classical.Basic
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4WhiteheadSketch
import Theorems.Thm_SP4WhiteheadSketch_compression_lemma
import Theorems.Thm_SP4WhiteheadSketch_cellular_approximation

set_option autoImplicit false

open scoped ContinuousMap
open ContinuousMap
open SP4WhiteheadSketch

universe u

/-- The contractible case of Whitehead's theorem via cellular approximation and the
compression lemma.

A weakly contractible CW complex `Y` is nonempty; fix `y : Y`.  Cellular approximation
replaces the identity `id_Y` by a cellular self-map `g` with `id_Y ≃ g`.  The compression
lemma, applied to `g` against the weakly contractible target `Y` and the point `y`, gives
`g ≃ const y`.  Hence `id_Y ≃ const y`, i.e. the identity is nullhomotopic, which is
equivalent to `ContractibleSpace Y`. -/
theorem solution (Y : Type u) [TopologicalSpace Y] [T2Space Y]
    [Topology.CWComplex (Set.univ : Set Y)] (hY : SP4WeakHomotopy.WeaklyContractible Y) :
    ContractibleSpace Y := by
  obtain ⟨y⟩ := hY.1
  obtain ⟨g, hgcell, hfg⟩ :=
    cellular_approximation (X := Y) (Y := Y) (ContinuousMap.id Y)
  have hgconst : Homotopic g (ContinuousMap.const Y y) :=
    compression_lemma (X := Y) (Y := Y) y hY g hgcell
  exact (contractible_iff_id_nullhomotopic Y).mpr ⟨y, hfg.trans hgconst⟩
