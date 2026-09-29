-- Prove2me | solution 1 for PDivisibleGroup.surjOn_transition_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0ad70404-cbf7-5399-a434-36a82426f5dc

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_HopfKer
import Theorems.Thm_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "PDivisibleGroup.Tower.levelCast_rfl PDivisibleGroup.Tower.transitionLE_one PDivisibleGroup.Tower.transitionLE_zero PDivisibleGroup.Hopf.nsmulBialgHom_apply HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K]
    (p : ℕ) [Fact p.Prime] {h t : ℕ} (G : PDivisibleGroup R p h) (T : PDivisibleGroup R p t)
    (π : ∀ v : ℕ, G.level v →ₐc[R] T.level v) (hπ : ∀ v, Function.Surjective (π v))
    (hπt : ∀ v : ℕ, (T.transition v).comp (π (v + 1)) = (π v).comp (G.transition v))
    (v : ℕ) :
    Set.SurjOn (G.transition v) (HopfAlgebra.hopfKer (π (v + 1)) : Set (G.level (v + 1)))
      (HopfAlgebra.hopfKer (π v) : Set (G.level v)) :=
  PDivisibleGroup.surjOn_transition_hopfKer_of_surjective_of_comp_eq p G T π hπ hπt v

end S_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing
end P2MW
export P2MW.S_PDivisibleGroup_surjOn_transition_hopfKer_of_surjective_of_comp_eq_of_isPrincipalIdealRing (solution)
