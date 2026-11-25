-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Ydb1.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:55:12.285434+00:00
-- url     : https://prove2.me/submissions/9940a513-f0fb-406d-a8ed-191a5bdbb906

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtraExtra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace UpperTheory.Reformulated.B.Ydb1
theorem _root_.solution :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] {K S : Set G},
      IsCompact K →
        S ⊆ K →
          (1 : G) ∈ S →
            ∀ {Ψ φ : G → G},
              Continuous Ψ →
                (∀ x ∈ S, Ψ x ∈ S) →
                  (∀ x ∈ S, φ x ∈ S) →
                    (∀ (x y : G), (Ψ x)⁻¹ * Ψ y = φ (x⁻¹ * y)) →
                      ∀ {l : ℕ},
                        (0 : ℕ) < l →
                          (∀ (U : Set G), IsOpen U → (1 : G) ∈ U → ∃ (m₀ : ℕ), ∀ m ≥ m₀, ∀ x ∈ S, φ^[l * m] x ∈ U) →
                            ∃ v ∈ K, Ψ v = v := by
  intro G _ _ _ _ K S hK hSK h1 Ψ φ hΨ hΨS hφS hrel l _ hconv
  have hφ1 : φ 1 = 1 := by
    have := hrel 1 1
    rw [inv_mul_cancel, inv_one, one_mul] at this
    exact this.symm
  have hΨx : ∀ y, Ψ y = Ψ 1 * φ y := fun y => by
    have := hrel 1 y
    rw [inv_one, one_mul] at this
    rw [← this, mul_inv_cancel_left]
  have hd : ∀ x y, φ (x⁻¹ * y) = (φ x)⁻¹ * φ y := fun x y => by
    rw [← hrel x y, hΨx x, hΨx y, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  have hmul : ∀ p q, φ (p * q) = φ p * φ q := by
    intro p q
    have hinv : φ p⁻¹ = (φ p)⁻¹ := by
      have := hd p 1
      rw [mul_one, hφ1, mul_one] at this
      exact this
    have := hd p⁻¹ q
    rw [inv_inv, hinv, inv_inv] at this
    exact this
  have hit : ∀ n x, Ψ^[n] x = Ψ^[n] 1 * φ^[n] x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih x, hΨx (Ψ^[n] 1 * φ^[n] x), hΨx (Ψ^[n] 1), hmul, mul_assoc]
  have ha : Ψ 1 ∈ S := hΨS 1 h1
  have hPS : ∀ n, Ψ^[n] 1 ∈ S := fun n => (Set.MapsTo.iterate (f := Ψ) hΨS n) h1
  have hφa : ∀ n, φ^[n] (Ψ 1) ∈ S := fun n => (Set.MapsTo.iterate (f := φ) hφS n) ha
  have hstep : ∀ n, Ψ (Ψ^[n] 1) = Ψ^[n] 1 * φ^[n] (Ψ 1) := fun n => by
    rw [← Function.iterate_succ_apply' Ψ n 1, Function.iterate_succ_apply, hit]
  have hlim : Tendsto (fun m : ℕ => φ^[l * m] (Ψ 1)) atTop (𝓝 1) := by
    rw [(nhds_basis_opens (1 : G)).tendsto_right_iff]
    rintro U ⟨h1U, hU⟩
    obtain ⟨m₀, hm₀⟩ := hconv U hU h1U
    exact eventually_atTop.2 ⟨m₀, fun m hm => hm₀ m hm _ ha⟩
  obtain ⟨v, hvK, hv⟩ := hK.exists_mapClusterPt (f := (atTop : Filter ℕ))
    (u := fun m : ℕ => Ψ^[l * m] 1)
    (by
      rw [le_principal_iff, mem_map]
      exact univ_mem' fun m => hSK (hPS (l * m)))
  obtain ⟨𝒰, h𝒰, hu⟩ := mapClusterPt_iff_ultrafilter.1 hv
  refine ⟨v, hvK, ?_⟩
  have h₁ : Tendsto (fun m : ℕ => Ψ (Ψ^[l * m] 1)) 𝒰 (𝓝 (Ψ v)) := (hΨ.tendsto v).comp hu
  have h₂ : Tendsto (fun m : ℕ => Ψ (Ψ^[l * m] 1)) 𝒰 (𝓝 (v * 1)) := by
    simp_rw [hstep]
    exact hu.mul (hlim.mono_left h𝒰)
  rw [mul_one] at h₂
  exact tendsto_nhds_unique h₁ h₂
end UpperTheory.Reformulated.B.Ydb1
