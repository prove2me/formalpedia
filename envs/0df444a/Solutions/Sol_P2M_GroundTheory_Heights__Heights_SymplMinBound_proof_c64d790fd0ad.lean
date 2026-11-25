-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplMinBound_proof_c64d790fd0ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:06.079813+00:00
-- url     : https://prove2.me/submissions/b84e819f-dd98-4701-8570-ad5c13aed6ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplMinBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplMinBound_exists_lt_a592eb1614ec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace SymplMinBound
theorem _root_.solution (h1 : SymplQuadDiag.Statement) (h2 : SymplMinkowskiBox.Statement) :
    SymplMinBound.Statement := by
  intro ι _ _ G hG hdet m hm
  obtain ⟨w, hw, -⟩ := hm.1
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hw (funext fun i => (IsEmpty.false i).elim)
  obtain ⟨O, lam, hlam, hO, hprod, hq⟩ := h1 ι G hG
  rw [hdet] at hprod
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have key : ∀ c : ℝ, 1 < c → m < (Fintype.card ι : ℝ) * c ^ 2 := by
    intro c hc
    obtain ⟨v, hv, hlt⟩ := PSymplMinBound.exists_lt h2 O lam hlam hO hprod c hc
    have hmv : m ≤ qf G (intVec v) := hm.2 ⟨v, hv, rfl⟩
    rw [hq] at hmv
    linarith
  by_contra hcon
  rw [not_le] at hcon
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set t : ℝ := (m / N + 1) / 2 with htdef
  have hmN : 1 < m / N := by rw [lt_div_iff₀ hN]; linarith
  have ht : 1 < t := by rw [htdef]; linarith
  have hsqrt : 1 < Real.sqrt t := by
    rw [Real.lt_sqrt zero_le_one]; linarith
  have hk := key (Real.sqrt t) hsqrt
  rw [Real.sq_sqrt (by linarith)] at hk
  have : N * t = (m + N) / 2 := by
    rw [htdef]; field_simp
  linarith
end SymplMinBound
end GroundTheory.Heights₂.Heights
