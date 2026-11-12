-- Prove2me | solution 1 for QEC.Coding.BDL26CSSDaviesLocality.sector_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:04:25.5082+00:00
-- url     : https://prove2.me/submissions/ab9a24ec-214e-411e-8010-9258de6b70b0

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Gibbs
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
import Definitions.Def_QEC_Coding_CSS_DaviesLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_DaviesLocality
import Theorems.Thm_QEC_Coding_BDL26CSSHamiltonian_hamiltonian_sector_energy


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CSSDaviesLocality
open Classical BDL26FiniteTannerSquare BDL26CSSHamiltonian
open PauliSymplectic Semantics Locality Semantics.Davies
open scoped BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26CSSDaviesLocality
theorem _root_.solution (u : Word (ZMod 2) (ZLabel S n))
    (v : Word (ZMod 2) (XLabel S n)) :
    BDL26CSSHamiltonian.hamiltonian S n * projector S n (CSSGibbs.joinSyndrome u v) =
      (((-((Fintype.card (ZLabel S n) + Fintype.card (XLabel S n) : Nat) : ℝ) +
        2 * ((HammingWeight u : ℝ) + (HammingWeight v : ℝ))) : ℝ) : ℂ) •
          projector S n (CSSGibbs.joinSyndrome u v) :=
  hamiltonian_sector_energy S n u v
end QEC.Coding.BDL26CSSDaviesLocality
