-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.canonical_seed_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:17:29.390202+00:00
-- url     : https://prove2.me/submissions/151faad1-5ec6-4952-962b-ebf0fa7bcc38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_canonical_prefix_word
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution : (canonicalGenerator S 0).val = BDL26LevelTwoDistance.seedCocycle := by
  have hbase :
      (BDL26AlternatingCochain.map1 S 0 BDL26SeedCohomology.seedElement.val :
        Word (ZMod 2) (Physical S 0)) =
      (BDL26LevelTwoDistance.seedCocycle : Word (ZMod 2) (Physical S 0)) := rfl
  exact Eq.trans (canonical_prefix_word S 0) hbase
end QEC.Coding.BDL26BareLogicalPair
