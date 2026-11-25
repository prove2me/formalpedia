-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleDegree_proof_8023612bf403
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:07.827039+00:00
-- url     : https://prove2.me/submissions/c395509c-a9c5-4e51-98ec-79cf4a5630ce

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDimSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSecsSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleHilbertSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleDegreeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_twistSys_one_40d8ce118432


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleDegree
theorem _root_.solution (hDim : VeryAmpleDim.Statement.{u, w})
    (hSecs : VeryAmpleSecs.Statement.{u, w}) (hHilb : VeryAmpleHilbert.Statement.{u, w}) :
    VeryAmpleDegree.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hZ hV
  obtain ⟨-, P, -, hP, hPn⟩ := hHilb k Ω N x e Nb hZ ⟨r, h, hV⟩
  obtain ⟨-, Q, -, hQ, hQn⟩ := hHilb k Ω r h e (twistBundle k h 1) (hDim k Ω N x e Nb r h hZ hV)
    isVeryAmple_twistSys_one
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hPn.and hQn)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have : a + n₀ = b + n₀ := by simpa using hab
      omega
    · intro m
      obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (Nat.le_add_left n₀ m)
      change P.eval _ = Q.eval _
      rw [← h1, ← h2, hSecs k Ω N x Nb r h hV (m + n₀)]
      rfl
  have hnum : (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) =
      (interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1) : ℚ) := by
    rw [← hP, hPQ, hQ]
    rfl
  exact_mod_cast hnum
end VeryAmpleDegree
end GroundTheory.Heights₂.Heights.Kleiman
