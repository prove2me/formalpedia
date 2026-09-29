-- Prove2me | solution 1 for RingHom.isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bf776961-d81b-5444-a13a-eb8c523c7884

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RingHom_isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing B]
    (σ₀ σ₁ : A →+* B) (ι₀ ι₁ : B → A)
    (h₀ : ∀ b, σ₀ (ι₀ b) = b) (h₁ : ∀ b, σ₁ (ι₁ b) = b)
    (p : ℕ) (hp : 2 ≤ p) (h₀₁ : ∀ b, ∃ c, σ₀ (ι₁ b) = c ^ p) :
    IsReduced (A ⧸ (RingHom.ker σ₀ ⊔ RingHom.ker σ₁)) := by
  classical
  have hσ₀ : Function.Surjective σ₀ := fun b => ⟨ι₀ b, h₀ b⟩
  have hσ₁ : Function.Surjective σ₁ := fun b => ⟨ι₁ b, h₁ b⟩

  set I : Ideal B := Ideal.map σ₀ (RingHom.ker σ₁) with hI

  have key : ∀ 𝔫 : Ideal B, 𝔫.IsMaximal → I ≤ 𝔫 → 𝔫 ≤ I ⊔ 𝔫 ^ 2 := by
    intro 𝔫 h𝔫 hI𝔫 s hs

    have hker₁ : ∀ x, x ∈ RingHom.ker σ₁ → σ₀ x ∈ 𝔫 := fun x hx =>
      hI𝔫 (Ideal.mem_map_of_mem σ₀ hx)

    set t : B := σ₁ (ι₀ s) with ht
    have hι₀ : σ₀ (ι₀ s) ∈ 𝔫 := by rw [h₀]; exact hs
    have hmem : σ₀ (ι₁ t) ∈ 𝔫 := by

      have hdiff : ι₁ t - ι₀ s ∈ RingHom.ker σ₁ := by
        rw [RingHom.mem_ker, map_sub, h₁, ht, sub_self]
      have := hker₁ _ hdiff
      rw [map_sub] at this
      simpa using 𝔫.add_mem this hι₀
    obtain ⟨c, hc⟩ := h₀₁ t
    rw [hc] at hmem
    have hc𝔫 : c ∈ 𝔫 := h𝔫.isPrime.mem_of_pow_mem p hmem
    have hcp : c ^ p ∈ 𝔫 ^ 2 := Ideal.pow_le_pow_right hp (Ideal.pow_mem_pow hc𝔫 p)

    have ha : ι₀ s - ι₁ t ∈ RingHom.ker σ₁ := by
      rw [RingHom.mem_ker, map_sub, h₁, ht, sub_self]
    have hs_eq : s = σ₀ (ι₀ s - ι₁ t) + c ^ p := by
      rw [map_sub, h₀, hc]; ring
    rw [hs_eq]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem σ₀ ha)) (Ideal.mem_sup_right hcp)

  have hR : ∀ J : Ideal (B ⧸ I), J.IsMaximal → ∃ e : B ⧸ I, IsIdempotentElem e ∧ J = Ideal.span {e} := by
    intro J hJ
    have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
    set 𝔫 : Ideal B := J.comap (Ideal.Quotient.mk I) with h𝔫
    have h𝔫max : 𝔫.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hmk
    have hI𝔫 : I ≤ 𝔫 := by
      intro x hx
      rw [h𝔫, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact J.zero_mem
    have hJ𝔫 : Ideal.map (Ideal.Quotient.mk I) 𝔫 = J := Ideal.map_comap_of_surjective _ hmk J
    have hidem : IsIdempotentElem J := by
      have h1 : J ≤ J * J := by
        calc J = Ideal.map (Ideal.Quotient.mk I) 𝔫 := hJ𝔫.symm
          _ ≤ Ideal.map (Ideal.Quotient.mk I) (I ⊔ 𝔫 ^ 2) := Ideal.map_mono (key 𝔫 h𝔫max hI𝔫)
          _ = J * J := by
            rw [Ideal.map_sup, Ideal.map_pow, hJ𝔫, Ideal.map_quotient_self, bot_sup_eq, pow_two]
      exact le_antisymm Ideal.mul_le_right h1
    have hfg : J.FG := (isNoetherian_def.mp inferInstance) J
    obtain ⟨e, he, hJe⟩ := (Ideal.isIdempotentElem_iff_of_fg J hfg).mp hidem
    exact ⟨e, he, by rw [hJe]⟩

  have hred : IsReduced (B ⧸ I) := by
    refine ⟨fun x hx => ?_⟩
    apply eq_zero_of_localization
    intro J hJ
    obtain ⟨e, he, hJe⟩ := hR J hJ
    have hxJ : x ∈ J := by
      have : x ∈ nilradical (B ⧸ I) := hx
      exact nilradical_le_prime J this
    rw [hJe] at hxJ
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hxJ
    have h1e : (1 - e) ∉ J := by
      intro h
      apply hJ.ne_top
      rw [Ideal.eq_top_iff_one]
      have : (1 : B ⧸ I) = (1 - e) + e := by ring
      rw [this]
      exact J.add_mem h (by rw [hJe]; exact Ideal.mem_span_singleton_self e)
    rw [IsLocalization.map_eq_zero_iff J.primeCompl]
    refine ⟨⟨1 - e, h1e⟩, ?_⟩
    show (1 - e) * (r * e) = 0
    have : e * e = e := he
    linear_combination (-r) * this

  let φ : A →+* B ⧸ I := (Ideal.Quotient.mk I).comp σ₀
  have hφ : ∀ a, a ∈ RingHom.ker σ₀ ⊔ RingHom.ker σ₁ → φ a = 0 := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp ha
    have hφxy : φ (x + y) = Ideal.Quotient.mk I (σ₀ y) := by
      simp [φ, RingHom.mem_ker.mp hx]
    rw [hφxy, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem σ₀ hy
  have hkerφ : RingHom.ker φ ≤ RingHom.ker σ₀ ⊔ RingHom.ker σ₁ := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    simp only [φ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at ha
    rw [hI, Ideal.mem_map_iff_of_surjective σ₀ hσ₀] at ha
    obtain ⟨y, hy, hya⟩ := ha
    have : a - y ∈ RingHom.ker σ₀ := by rw [RingHom.mem_ker, map_sub, hya, sub_self]
    have : a = (a - y) + y := by ring
    rw [this]
    exact Submodule.add_mem_sup ‹a - y ∈ RingHom.ker σ₀› hy
  have hinj : Function.Injective (Ideal.Quotient.lift (RingHom.ker σ₀ ⊔ RingHom.ker σ₁) φ hφ) :=
    RingHom.lift_injective_of_ker_le_ideal _ hφ hkerφ
  exact isReduced_of_injective _ hinj

end S_RingHom_isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow
end P2MW
export P2MW.S_RingHom_isReduced_quotient_ker_sup_ker_of_exists_apply_eq_pow (solution)
