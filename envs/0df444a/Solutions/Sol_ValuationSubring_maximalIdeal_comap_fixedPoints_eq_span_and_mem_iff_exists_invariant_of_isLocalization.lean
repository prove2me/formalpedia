-- Prove2me | solution 1 for ValuationSubring.maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/754fbf05-c062-5a99-8d3e-cd1f324e2711

import Mathlib
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedPoints_and_exists_uniformizer_and_residue_descent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] (G : Type) [Group G] [Finite G] [MulSemiringAction G K]
    (W : ValuationSubring K) [IsDiscreteValuationRing W]

    (π : K) (hπG : ∀ g : G, g • π = π) (hπW : π ∈ W)
    (hπ : IsLocalRing.maximalIdeal W = Ideal.span {(⟨π, hπW⟩ : W)})

    (hfaith : ∀ (g : G) (hg : ∀ x : K, g • x ∈ W ↔ x ∈ W), g ≠ 1 → ∃ x : W,
      (⟨g • (x : K), (hg x).mpr x.2⟩ - x : W) ∉ IsLocalRing.maximalIdeal W)

    (B : Subring K) (hBG : ∀ (g : G) (b : K), b ∈ B → g • b ∈ B) (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧
      (∀ hh : h ∈ W, (⟨h, hh⟩ : W) ∉ IsLocalRing.maximalIdeal W) ∧ f * h = g) :

    IsDiscreteValuationRing (W.comap (FixedPoints.subfield G K).subtype) ∧

    (∃ hπ0 : (⟨π, fun g => hπG g⟩ : FixedPoints.subfield G K) ∈ W.comap (FixedPoints.subfield G K).subtype,
      IsLocalRing.maximalIdeal (W.comap (FixedPoints.subfield G K).subtype) = Ideal.span {(⟨_, hπ0⟩ : W.comap (FixedPoints.subfield G K).subtype)}) ∧

    (∀ f : K, (∀ g : G, g • f = f) →
      (f ∈ W ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ σ : G, σ • g = g) ∧ (∀ σ : G, σ • h = h) ∧
        (∀ hh : h ∈ W, (⟨h, hh⟩ : W) ∉ IsLocalRing.maximalIdeal W) ∧ f * h = g)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨hdvr, -, -⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedPoints_and_exists_uniformizer_and_residue_descent K G W hfaith
  haveI := hdvr
  have hπne : π ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field' (R := ↥W)
    rw [hπ, Ideal.span_singleton_eq_bot]
    exact Subtype.ext h0
  have hπmax : (⟨π, hπW⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W := by
    rw [hπ]; exact Ideal.mem_span_singleton_self _
  refine ⟨hdvr, ?_, ?_⟩
  ·
    have hπ0 : (⟨π, fun g => hπG g⟩ : FixedPoints.subfield G K) ∈ W.comap (FixedPoints.subfield G K).subtype := hπW
    refine ⟨hπ0, ?_⟩

    let ι : ↥(W.comap (FixedPoints.subfield G K).subtype) →+* ↥W :=
      { toFun := fun x => ⟨((x : FixedPoints.subfield G K) : K), x.2⟩
        map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
    apply le_antisymm
    · intro x hx
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx

      have hxW : (⟨((x : FixedPoints.subfield G K) : K), x.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        apply hx
        obtain ⟨u, hu⟩ := hu
        have hxK0 : ((x : FixedPoints.subfield G K) : K) ≠ 0 := by
          intro h0; apply u.ne_zero; rw [hu]; exact Subtype.ext h0
        have hx0' : (x : FixedPoints.subfield G K) ≠ 0 := fun h0 => hxK0 (by rw [h0]; rfl)
        have e : (((u⁻¹ : (↥W)ˣ) : ↥W) : K) * ((x : FixedPoints.subfield G K) : K) = 1 := by
          have := congrArg (fun z : ↥W => (z : K)) u.inv_mul
          rw [hu] at this
          exact this
        have hinv : (((x : FixedPoints.subfield G K) : K))⁻¹ ∈ W := by
          rw [← (eq_inv_of_mul_eq_one_left e)]
          exact ((u⁻¹ : (↥W)ˣ) : ↥W).2
        have hinv0 : ((x : FixedPoints.subfield G K))⁻¹ ∈ W.comap (FixedPoints.subfield G K).subtype := by
          change (FixedPoints.subfield G K).subtype (x : FixedPoints.subfield G K)⁻¹ ∈ W
          rw [map_inv₀]; exact hinv
        exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinv0⟩, Subtype.ext (mul_inv_cancel₀ hx0')⟩
      rw [hπ, Ideal.mem_span_singleton'] at hxW
      obtain ⟨y, hy⟩ := hxW
      have hyK : (y : K) * π = ((x : FixedPoints.subfield G K) : K) := congrArg Subtype.val hy
      have hyG : ∀ g : G, g • (y : K) = y := by
        intro g
        have : (y : K) = ((x : FixedPoints.subfield G K) : K) * π⁻¹ := by
          rw [← hyK, mul_inv_cancel_right₀ hπne]
        rw [this, smul_mul', smul_inv'', hπG g, (x : FixedPoints.subfield G K).2 g]
      rw [Ideal.mem_span_singleton']
      refine ⟨⟨⟨(y : K), hyG⟩, y.2⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      exact hyK
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).mp hπmax (hu.map ι)
  ·
    intro f hfG
    constructor
    · intro hfW

      let I : Ideal ↥B :=
        { carrier := {h | f * (h : K) ∈ B}
          add_mem' := fun {a b} ha hb => by
            change f * ((a : K) + b) ∈ B
            rw [mul_add]; exact B.add_mem ha hb
          zero_mem' := by change f * (0 : K) ∈ B; rw [mul_zero]; exact B.zero_mem
          smul_mem' := fun c {a} ha => by
            change f * ((c : K) * a) ∈ B
            rw [mul_left_comm]; exact B.mul_mem c.2 ha }
      have memI : ∀ h : ↥B, h ∈ I ↔ f * (h : K) ∈ B := fun _ => Iff.rfl

      let φ : G → (↥B →+* ↥W) := fun σ =>
        { toFun := fun b => ⟨σ • (b : K), hBW _ (hBG σ _ b.2)⟩
          map_one' := Subtype.ext (by change σ • ((1 : ↥B) : K) = 1; rw [OneMemClass.coe_one, smul_one])
          map_mul' := fun a b => Subtype.ext (by change σ • ((a : K) * b) = σ • (a : K) * σ • (b : K); rw [smul_mul'])
          map_zero' := Subtype.ext (by change σ • ((0 : ↥B) : K) = 0; rw [ZeroMemClass.coe_zero, smul_zero])
          map_add' := fun a b => Subtype.ext (by change σ • ((a : K) + b) = σ • (a : K) + σ • (b : K); rw [smul_add]) }
      have hφ : ∀ (σ : G) (b : ↥B), (φ σ b : K) = σ • (b : K) := fun _ _ => rfl
      let Q : G → Ideal ↥B := fun σ => Ideal.comap (φ σ) (IsLocalRing.maximalIdeal ↥W)
      have hQprime : ∀ σ, (Q σ).IsPrime := fun σ => Ideal.comap_isPrime (φ σ) _
      have memQ : ∀ (σ : G) (b : ↥B), b ∈ Q σ ↔ (⟨σ • (b : K), hBW _ (hBG σ _ b.2)⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W :=
        fun _ _ => Iff.rfl

      obtain ⟨g₁, h₁, hg₁B, hh₁B, hh₁u, hfh₁⟩ := (hloc f).mp hfW
      have hnot : ∀ σ : G, ¬ (I ≤ Q σ) := by
        intro σ hle
        have hmem : (⟨σ⁻¹ • h₁, hBG _ _ hh₁B⟩ : ↥B) ∈ I := by
          rw [memI]
          change f * (σ⁻¹ • h₁) ∈ B
          have : f * (σ⁻¹ • h₁) = σ⁻¹ • (f * h₁) := by rw [smul_mul', hfG σ⁻¹]
          rw [this, hfh₁]; exact hBG _ _ hg₁B
        have h2 := hle hmem
        rw [memQ] at h2
        apply hh₁u (hBW _ hh₁B)
        have e : (⟨σ • ((⟨σ⁻¹ • h₁, hBG _ _ hh₁B⟩ : ↥B) : K), hBW _ (hBG σ _ (hBG _ _ hh₁B))⟩ : ↥W) = ⟨h₁, hBW _ hh₁B⟩ := by
          apply Subtype.ext; change σ • σ⁻¹ • h₁ = h₁; rw [smul_inv_smul]
        rw [← e]; exact h2

      have havoid : ¬ ((I : Set ↥B) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset G) : Set G), ((Q σ) : Set ↥B)) := by
        rw [Ideal.subset_union_prime (1 : G) (1 : G) (fun σ _ _ _ => hQprime σ)]
        rintro ⟨σ, -, hle⟩
        exact hnot σ hle
      rw [Set.not_subset] at havoid
      obtain ⟨h, hhI, hhQ⟩ := havoid
      have hhQ' : ∀ σ : G, h ∉ Q σ := by
        intro σ hσ
        apply hhQ
        rw [Set.mem_iUnion₂]
        exact ⟨σ, Finset.mem_coe.mpr (Finset.mem_univ σ), hσ⟩
      have hfhB : f * (h : K) ∈ B := (memI h).mp hhI

      have hσhB : ∀ σ : G, σ • (h : K) ∈ B := fun σ => hBG σ _ h.2
      have hσhu : ∀ σ : G, (⟨σ • (h : K), hBW _ (hσhB σ)⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W :=
        fun σ hσ => hhQ' σ ((memQ σ h).mpr hσ)
      set hp : K := ∏ σ : G, σ • (h : K) with hhp
      have hp_B : hp ∈ B := Subring.prod_mem B (fun σ _ => hσhB σ)
      have hp_W : hp ∈ W := hBW _ hp_B
      have hpW_eq : ∀ hh : hp ∈ W, (⟨hp, hh⟩ : ↥W) = ∏ σ : G, (⟨σ • (h : K), hBW _ (hσhB σ)⟩ : ↥W) := by
        intro hh
        apply Subtype.ext
        change hp = W.subtype (∏ σ : G, (⟨σ • (h : K), hBW _ (hσhB σ)⟩ : ↥W))
        rw [map_prod, hhp]
        rfl
      have hp_unit : ∀ hh : hp ∈ W, (⟨hp, hh⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W := by
        intro hh
        rw [hpW_eq hh]
        apply Finset.prod_induction (p := fun x : ↥W => x ∉ IsLocalRing.maximalIdeal ↥W)
        · intro a b ha hb
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at ha hb ⊢
          exact ha.mul hb
        · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]; exact isUnit_one
        · intro σ _; exact hσhu σ
      have hpG : ∀ τ : G, τ • hp = hp := by
        intro τ
        rw [hhp, Finset.smul_prod']
        simp_rw [smul_smul]
        exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
      have hg'B : f * hp ∈ B := by
        have : hp = (h : K) * ∏ σ ∈ (Finset.univ : Finset G).erase 1, σ • (h : K) := by
          rw [hhp, ← Finset.mul_prod_erase (Finset.univ : Finset G) (fun σ => σ • (h : K)) (Finset.mem_univ 1), one_smul]
        rw [this, ← mul_assoc]
        exact B.mul_mem hfhB (Subring.prod_mem B (fun σ _ => hσhB σ))
      refine ⟨f * hp, hp, hg'B, hp_B, fun σ => ?_, hpG, hp_unit, rfl⟩
      rw [smul_mul', hfG, hpG]
    · rintro ⟨g, h, hgB, hhB, -, -, hhu, hfh⟩
      exact (hloc f).mpr ⟨g, h, hgB, hhB, hhu, hfh⟩

end S_ValuationSubring_maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization
end P2MW
export P2MW.S_ValuationSubring_maximalIdeal_comap_fixedPoints_eq_span_and_mem_iff_exists_invariant_of_isLocalization (solution)
