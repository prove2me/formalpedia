-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_VeryAmpleSnapper_proof_c990f3b5fcc4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:41.95314+00:00
-- url     : https://prove2.me/submissions/fb46761b-4732-440d-839d-fc8777c4a9ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSnapper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_VeryAmpleSnapperSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleSnapper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eulerChar_eq_finrank_H0_8f9d9dde05af
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CechZerothCohomologySections_proof_666dbd5f83b0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


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
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace VeryAmpleSnapper
theorem _root_.solution (hF : SnapperFinite.Statement.{u, w, w}) (hS : Snapper.Statement.{u, w, w})
    (hV : TwistVanishAll.Statement.{u, w}) (hA : AmpleVanish.Statement.{u, w, w}) :
    VeryAmpleSnapper.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hNb
  obtain ⟨r, h, hh⟩ := hNb
  have hx : x ≠ 0 := by
    obtain ⟨i, hi⟩ := hZ.relevant
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X k i), aeval_X] at hi
    exact fun h0 => hi (congrFun h0 i)
  set O := twistBundle k x 0
  have hsys : ∀ (a : ℕ) (c : ℤ), (O.toSubSystem.twistPows 1 (fun j => (![Nb] j).toSubSystem)
      (fun _ => a)).twist (twistSys k x c) = twistMul Nb.toSubSystem a c := by
    intro a c
    change ((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _ = _
    rw [twistSys_zero_twist]
    rfl
  have hpt : ∀ a c : ℚ, (Fin.snoc (α := fun _ => ℚ) (fun _ : Fin 1 => a) c : Fin 2 → ℚ) = ![a, c] := by
    intro a c; funext i; fin_cases i <;> rfl
  have h0 : ∀ F : SubSystem k x Ω, Module.finrank k (F.H 0) = Module.finrank k F.secs := fun F =>
    (CechZerothCohomologySections.proof k Ω N x Ω F hx).some.finrank_eq
  obtain ⟨Q, hQ, hχ⟩ := hS k Ω N x e hZ Ω O.toSubFamily O.fg 1 ![Nb]
  obtain ⟨c₀, hc₀⟩ := hV k Ω N x O Nb r h hh.mem_secs hh.generates
  obtain ⟨a₀, ha₀⟩ := hA k Ω N x Ω O.toSubFamily O.fg Nb ⟨r, h, hh⟩
  refine ⟨fun a c => ?_, Q, c₀, hQ, fun a c hc => ?_, ?_⟩
  · have := hF k Ω N x Ω O.toSubFamily O.fg 1 ![Nb] (fun _ => a) c 0
    rw [hsys] at this
    exact (CechZerothCohomologySections.proof k Ω N x Ω _ hx).some.finiteDimensional
  · have hv : ∀ i, 1 ≤ i → Subsingleton ((twistMul Nb.toSubSystem a c).H i) := by
      intro i hi
      have := hc₀ i a c hi hc
      change Subsingleton ((((twistSys k x 0).twist (Nb.toSubSystem.pow a)).twist _).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) c
    rw [hsys, hpt, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this
  · filter_upwards [eventually_ge_atTop a₀] with a ha
    have hv : ∀ i, 1 ≤ i → Subsingleton ((Nb.toSubSystem.pow a).H i) := by
      intro i hi
      have := ha₀ i a hi ha
      change Subsingleton (((twistSys k x 0).twist (Nb.toSubSystem.pow a)).H i) at this
      rwa [twistSys_zero_twist] at this
    have := hχ (fun _ => a) 0
    rw [hsys, hpt, twistMul, SubSystem.twist_twistSys_zero, eulerChar_eq_finrank_H0 _ hv, h0] at this
    exact_mod_cast this
end VeryAmpleSnapper
end GroundTheory.Heights₂.Heights.Kleiman
