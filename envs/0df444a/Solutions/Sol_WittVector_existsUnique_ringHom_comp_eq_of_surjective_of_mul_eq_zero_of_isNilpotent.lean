-- Prove2me | solution 1 for WittVector.existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/bdcc980e-5229-54e7-b869-7f2cca4539a2

import Mathlib
import Theorems.Thm_WittVector_existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent

set_option autoImplicit false

universe u

open WittVector

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (B B₀ : Type u) [CommRing B] [CommRing B₀] (q : B →+* B₀) (hq : Function.Surjective q)
    (hsq : ∀ s t : B, q s = 0 → q t = 0 → s * t = 0) (hpB : IsNilpotent (p : B))
    (ψ₀ : WittVector p k →+* B₀) :
    ∃! ψ : WittVector p k →+* B, q.comp ψ = ψ₀ := by
  classical
  obtain ⟨M₀, hM₀⟩ := hpB
  set M := M₀ + 1 with hMdef
  have hM : (p : B) ^ M = 0 := by rw [hMdef, pow_succ, hM₀, zero_mul]
  have hM' : (p : B₀) ^ M = 0 := by
    have := congrArg q hM
    rwa [map_pow, map_natCast, map_zero] at this
  have hMk : (p : k) ^ M = 0 := by
    rw [hMdef, pow_succ, CharP.cast_eq_zero, mul_zero]

  let J : Ideal (WittVector p k) := Ideal.span {((p : WittVector p k) ^ M)}
  have hJ : ∀ {C : Type u} [CommRing C] (g : WittVector p k →+* C), (p : C) ^ M = 0 → ∀ a ∈ J, g a = 0 := by
    intro C _ g hg a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, map_pow, map_natCast, hg, mul_zero]
  let ψ₀' : WittVector p k ⧸ J →+* B₀ := Ideal.Quotient.lift J ψ₀ (hJ ψ₀ hM')
  let cc' : WittVector p k ⧸ J →+* k := Ideal.Quotient.lift J (constantCoeff : WittVector p k →+* k) (hJ _ hMk)
  have hψ₀' : ψ₀'.comp (Ideal.Quotient.mk J) = ψ₀ := Ideal.Quotient.lift_comp_mk _ _ _
  have hcc' : cc'.comp (Ideal.Quotient.mk J) = constantCoeff := Ideal.Quotient.lift_comp_mk _ _ _

  have hker_cc' : ∀ w : WittVector p k ⧸ J, cc' w = 0 → ∃ v : WittVector p k ⧸ J, w = (p : WittVector p k ⧸ J) * v := by
    intro w hw
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hw' : constantCoeff w = 0 := by
      have : (cc'.comp (Ideal.Quotient.mk J)) w = 0 := hw
      rwa [hcc'] at this
    have : w ∈ RingHom.ker (constantCoeff : WittVector p k →+* k) := hw'
    rw [ker_constantCoeff, Ideal.mem_span_singleton'] at this
    obtain ⟨v, rfl⟩ := this
    exact ⟨Ideal.Quotient.mk J v, by rw [map_mul, map_natCast, mul_comm]⟩
  have hpM_WM : (p : WittVector p k ⧸ J) ^ M = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk J), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl

  let P : Subring (B × (WittVector p k ⧸ J)) :=
    RingHom.eqLocus (q.comp (RingHom.fst B (WittVector p k ⧸ J))) (ψ₀'.comp (RingHom.snd B (WittVector p k ⧸ J)))
  have hPmem : ∀ x : B × (WittVector p k ⧸ J), x ∈ P ↔ q x.1 = ψ₀' x.2 := fun x => Iff.rfl
  let prB : P →+* B := (RingHom.fst B (WittVector p k ⧸ J)).comp P.subtype
  let prW : P →+* WittVector p k ⧸ J := (RingHom.snd B (WittVector p k ⧸ J)).comp P.subtype
  have hPcomm : q.comp prB = ψ₀'.comp prW := by
    ext x
    exact (hPmem x.1).mp x.2
  let ρ : P →+* k := cc'.comp prW

  have hρs : Function.Surjective ρ := by
    intro a
    obtain ⟨w, hw⟩ := constantCoeff_surjective (p := p) (R := k) a
    obtain ⟨b, hb⟩ := hq (ψ₀ w)
    refine ⟨⟨(b, Ideal.Quotient.mk J w), ?_⟩, ?_⟩
    · show q b = ψ₀' (Ideal.Quotient.mk J w)
      rw [hb, ← hψ₀']
      rfl
    · show cc' (Ideal.Quotient.mk J w) = a
      rw [← hw, ← hcc']
      rfl

  have hρn : IsNilpotent (RingHom.ker ρ) := by

    have h1 : RingHom.ker ρ ≤ (Ideal.span {(p : WittVector p k ⧸ J)}).comap prW := by
      intro x hx
      obtain ⟨v, hv⟩ := hker_cc' (prW x) hx
      rw [Ideal.mem_comap, hv]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
    have h2 : (RingHom.ker ρ) ^ M ≤ RingHom.ker prW := by
      refine (Ideal.pow_right_mono h1 M).trans ?_
      refine (Ideal.le_comap_pow _ M).trans ?_
      rw [Ideal.span_singleton_pow, hpM_WM, Ideal.span_singleton_zero]
      intro x hx
      exact hx
    have h3 : (RingHom.ker prW) ^ 2 = ⊥ := by
      rw [pow_two, ← le_bot_iff, Ideal.mul_le]
      intro x hx y hy
      rw [Ideal.mem_bot]
      have hx1 : q (prB x) = 0 := by
        have := congrArg (fun φ : P →+* B₀ => φ x) hPcomm
        simp only [RingHom.comp_apply] at this
        rw [this, RingHom.mem_ker.mp hx, map_zero]
      have hy1 : q (prB y) = 0 := by
        have := congrArg (fun φ : P →+* B₀ => φ y) hPcomm
        simp only [RingHom.comp_apply] at this
        rw [this, RingHom.mem_ker.mp hy, map_zero]
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact hsq _ _ hx1 hy1
      · show prW (x * y) = 0
        rw [map_mul, RingHom.mem_ker.mp hx, zero_mul]
    refine ⟨2 * M, ?_⟩
    rw [mul_comm, pow_mul]
    exact le_bot_iff.mp ((Ideal.pow_right_mono h2 2).trans h3.le)

  obtain ⟨F, hF, hFu⟩ := WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker p k P ρ hρs hρn
  have hWMu : ∀ G : WittVector p k →+* WittVector p k ⧸ J, cc'.comp G = constantCoeff → G = Ideal.Quotient.mk J := by
    have hs : Function.Surjective cc' := fun a => by
      obtain ⟨w, hw⟩ := constantCoeff_surjective (p := p) (R := k) a
      exact ⟨Ideal.Quotient.mk J w, by rw [← hw, ← hcc']; rfl⟩
    have hn : IsNilpotent (RingHom.ker cc') := by
      refine ⟨M, ?_⟩
      have h1 : RingHom.ker cc' ≤ Ideal.span {(p : WittVector p k ⧸ J)} := by
        intro w hw
        obtain ⟨v, hv⟩ := hker_cc' w hw
        rw [hv]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
      apply le_bot_iff.mp
      refine (Ideal.pow_right_mono h1 M).trans ?_
      rw [Ideal.span_singleton_pow, hpM_WM, Ideal.span_singleton_zero]
    obtain ⟨G₀, -, hG₀u⟩ := WittVector.existsUnique_ringHom_comp_eq_constantCoeff_of_isNilpotent_ker p k (WittVector p k ⧸ J) cc' hs hn
    intro G hG
    rw [hG₀u G hG, hG₀u (Ideal.Quotient.mk J) hcc']
  have hFW : prW.comp F = Ideal.Quotient.mk J := by
    apply hWMu
    rw [← RingHom.comp_assoc]
    exact hF

  refine ⟨prB.comp F, ?_, ?_⟩
  · show q.comp (prB.comp F) = ψ₀
    rw [← RingHom.comp_assoc, hPcomm, RingHom.comp_assoc, hFW, hψ₀']
  · intro ψ hψ

    let F' : WittVector p k →+* P := (RingHom.prod ψ (Ideal.Quotient.mk J)).codRestrict P (fun w => by
      show q (ψ w) = ψ₀' (Ideal.Quotient.mk J w)
      rw [← RingHom.comp_apply, hψ, ← hψ₀']
      rfl)
    have hF' : ρ.comp F' = constantCoeff := by
      ext w
      show cc' (Ideal.Quotient.mk J w) = constantCoeff w
      rw [← hcc']
      rfl
    have : F' = F := hFu F' hF'
    rw [← this]
    rfl

end S_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent
end P2MW
export P2MW.S_WittVector_existsUnique_ringHom_comp_eq_of_surjective_of_mul_eq_zero_of_isNilpotent (solution)
