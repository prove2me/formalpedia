-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.orbClosed_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:42.154184+00:00
-- url     : https://prove2.me/submissions/2d4680f6-c5c1-4fa6-aff6-baad32b6f0df

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbB
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_isClosed_idem_rank
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_orbHom_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {N : ℕ}
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
theorem _root_.solution (N r : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (hA : IsReduced A)
    (b : Fin r → A) (hb : Submodule.span k (Set.range b) = ⊤) (ρ₀ : A →ₐ[k] Matrix (Fin N) (Fin N) k) :
    IsClosed {w : Fin r → Matrix (Fin N) (Fin N) k | ∃ g : GL (Fin N) k, ∀ i, w i = g.val * ρ₀ (b i) * g⁻¹.val} := by
  classical
  let L : (Fin r → k) → A := fun c => ∑ i, c i • b i
  let Φ : (Fin r → Matrix (Fin N) (Fin N) k) → (Fin r → k) → Matrix (Fin N) (Fin N) k :=
    fun w c => ∑ i, c i • w i
  have hL : ∀ a, ∃ c, L c = a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun k).1 (hb ▸ Submodule.mem_top)
  choose s hs using hL
  have Lsub : ∀ c c', L (c - c') = L c - L c' := fun c c' => by
    simp only [L, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φsub : ∀ w c c', Φ w (c - c') = Φ w c - Φ w c' := fun w c c' => by
    simp only [Φ, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φadd : ∀ w c c', Φ w (c + c') = Φ w c + Φ w c' := fun w c c' => by
    simp only [Φ, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have Φsmul : ∀ w (t : k) c, Φ w (t • c) = t • Φ w c := fun w t c => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have Lsingle : ∀ i, L (Pi.single i 1) = b i := fun i => by
    simp [L, Pi.single_apply]
  have Φsingle : ∀ w i, Φ w (Pi.single i 1) = w i := fun w i => by
    simp [Φ, Pi.single_apply]
  have hΦc : ∀ c : Fin r → k, Continuous fun w : Fin r → Matrix (Fin N) (Fin N) k => Φ w c := fun c =>
    continuous_finset_sum _ fun i _ => (continuous_apply i).const_smul (c i)
  let S : Set (Fin r → Matrix (Fin N) (Fin N) k) :=
    (⋂ c, ⋂ (_ : L c = 0), {w | Φ w c = 0}) ∩ ((⋂ a, ⋂ a', {w | Φ w (s (a * a')) = Φ w (s a) * Φ w (s a')}) ∩
      ({w | Φ w (s 1) = 1} ∩ ⋂ e, ⋂ (_ : IsIdempotentElem e),
        (fun w => Φ w (s e)) ⁻¹' {P | P * P = P ∧ P.rank = (ρ₀ e).rank}))
  have hS : IsClosed S := by
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_iInter fun c => isClosed_iInter fun _ => isClosed_eq (hΦc c) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun a' =>
        isClosed_eq (hΦc _) ((hΦc _).mul (hΦc _))
    · exact isClosed_eq (hΦc _) continuous_const
    · exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        (isClosed_idem_rank (ρ₀ e).rank).preimage (hΦc (s e))
  convert hS using 1
  ext w
  simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨g, hg⟩
    have hΦ : ∀ c, Φ w c = g.val * ρ₀ (L c) * g⁻¹.val := fun c => by
      simp only [Φ, L, hg, map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    have hgi : g⁻¹.val * g.val = 1 := Units.inv_mul g
    refine ⟨fun c hc => by rw [hΦ, hc, map_zero, mul_zero, zero_mul], fun a a' => ?_, ?_, fun e he => ?_⟩
    · rw [hΦ, hΦ, hΦ, hs, hs, hs, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul]
    · rw [hΦ, hs, map_one, mul_one, Units.mul_inv]
    · rw [hΦ, hs]
      refine ⟨?_, ?_⟩
      · have := congrArg ρ₀ he.eq
        rw [map_mul] at this
        simp only [mul_assoc]
        rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul, ← mul_assoc (ρ₀ e), this]
      · rw [rank_mul_eq_left_of_isUnit_det _ _ (isUnits_det_units g⁻¹),
          rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units g)]
  · rintro ⟨h0, hmul, h1, hrk⟩
    have hwd : ∀ c c', L c = L c' → Φ w c = Φ w c' := fun c c' h => by
      have := h0 (c - c') (by rw [Lsub, h, sub_self])
      rwa [Φsub, sub_eq_zero] at this
    let ρl : A →ₗ[k] Matrix (Fin N) (Fin N) k :=
      { toFun := fun a => Φ w (s a)
        map_add' := fun a a' => by
          rw [← Φadd]; apply hwd; rw [hs]
          simp only [L, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, show (∑ i, s a' i • b i) = L (s a') from rfl, hs, hs]
        map_smul' := fun t a => by
          rw [RingHom.id_apply, ← Φsmul]; apply hwd; rw [hs]
          simp only [L, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, hs] }
    let ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k := AlgHom.ofLinearMap ρl h1 hmul
    have hρ : ∀ a, ρ a = Φ w (s a) := fun _ => rfl
    obtain ⟨g, hg⟩ := orbHom_gen k N A hA ρ₀ ρ fun e he => by rw [hρ, (hrk e he).2]
    refine ⟨g, fun i => ?_⟩
    rw [← hg, hρ, ← Φsingle w i]
    apply hwd
    rw [hs, Lsingle]
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
