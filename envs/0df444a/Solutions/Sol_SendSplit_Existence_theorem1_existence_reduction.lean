-- Prove2me | solution 1 for SendSplit.Existence.theorem1_existence_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:14:01.811013+00:00
-- url     : https://prove2.me/submissions/08e01cca-d052-46f6-8033-7f1f681f3464

import Mathlib
import Definitions.Def_SendSplit_Existence_Network
import Definitions.Def_SendSplit_Existence_ReducedCost
import Definitions.Def_SendSplit_Existence_AugmentedGraph
import Theorems.Thm_SendSplit_Existence_hirsch_hoffman_extension
import Theorems.Thm_SendSplit_Existence_reducedFlowCost_eq
import Theorems.Thm_SendSplit_Existence_concave_sandwich
import Theorems.Thm_SendSplit_Existence_simpleCirculation_cost_nonneg_iff
import Theorems.Thm_SendSplit_Existence_extreme_circulation_iff_eq_zero
import Theorems.Thm_SendSplit_Existence_six_implies_seven_bounds
import Theorems.Thm_SendSplit_Existence_five_implies_six
import Theorems.Thm_SendSplit_Existence_six_implies_five

open SendSplit.Existence

namespace SSThm1Aux

variable {n : ℕ}

lemma arc_scale (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0) {a k : ℝ}
    (ha : 0 ≤ a) (hk : 1 ≤ k) : f (k * a) ≤ k * f a := by
  have hk0 : 0 < k := by linarith
  have hka : (0:ℝ) ≤ k * a := by positivity
  have := hf.2 (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 hka)
    (show (0:ℝ) ≤ 1 - 1/k by rw [sub_nonneg]; exact (div_le_one hk0).2 hk)
    (show (0:ℝ) ≤ 1/k by positivity) (show (1 - 1/k) + 1/k = (1:ℝ) by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, h0] at this
  have e : 1 / k * (k * a) = a := by field_simp
  rw [e] at this
  have := mul_le_mul_of_nonneg_left this hk0.le
  have e2 : k * (1 / k * f (k * a)) = f (k * a) := by field_simp
  linarith

lemma bounded_imp_nonneg (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) (y : Fin n → Fin n → ℝ) (hy : IsPreflow G y) (M : ℝ)
    (hM : ∀ θ : ℝ, 0 ≤ θ → M ≤ flowCost G c (fun i j => θ * y i j)) :
    ∀ θ : ℝ, 0 ≤ θ → 0 ≤ flowCost G c (fun i j => θ * y i j) := by
  intro θ hθ
  by_contra hneg
  push Not at hneg
  set φ := flowCost G c (fun i j => θ * y i j) with hφ
  have hscale : ∀ k : ℝ, 1 ≤ k → flowCost G c (fun i j => (k * θ) * y i j) ≤ k * φ := by
    intro k hk
    unfold flowCost at hφ ⊢
    rw [hφ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    show c p.1 p.2 (k * θ * y p.1 p.2) ≤ k * c p.1 p.2 (θ * y p.1 p.2)
    rw [mul_assoc]
    exact arc_scale _ (hc p hp).1 (hc p hp).2 (mul_nonneg hθ (hy.1 _ _)) hk
  set k := max 1 (M / φ + 1)
  have hk1 : 1 ≤ k := le_max_left _ _
  have hk2 : M / φ + 1 ≤ k := le_max_right _ _
  have h1 := hscale k hk1
  have h2 := hM (k * θ) (by positivity)
  have h3 : k * φ ≤ (M / φ + 1) * φ := mul_le_mul_of_nonpos_right hk2 hneg.le
  have hφne : φ ≠ 0 := hneg.ne
  have h4 : (M / φ + 1) * φ = M + φ := by field_simp
  linarith

lemma simple_scale (G : ArcGraph n) (y : Fin n → Fin n → ℝ) (hy : IsSimpleCirculation G y)
    (t : ℝ) (ht : 0 < t) : IsSimpleCirculation G (fun i j => t * y i j) := by
  obtain ⟨⟨⟨hnn, hoff⟩, hbal⟩, hcirc⟩ := hy
  refine ⟨⟨⟨fun i j => mul_nonneg ht.le (hnn i j), fun i j h => by simp [hoff i j h]⟩, ?_⟩, ?_⟩
  · intro i
    have := hbal i
    simp only at this ⊢
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub, this, mul_zero]
  · have : support G (fun i j => t * y i j) = support G y := by
      unfold support
      apply Finset.filter_congr
      intro p _
      simp [ht.ne']
    rw [this]; exact hcirc

lemma zero_isFlow (G : ArcGraph n) : IsFlow G (fun _ => 0) (fun _ _ => 0) := by
  simp [IsFlow, IsPreflow]

lemma flow_add_circ (G : ArcGraph n) (r : Fin n → ℝ) (x y : Fin n → Fin n → ℝ)
    (hx : IsFlow G r x) (hy : IsCirculation G y) (θ : ℝ) (hθ : 0 ≤ θ) :
    IsFlow G r (fun i j => x i j + θ * y i j) := by
  obtain ⟨⟨hxn, hxo⟩, hxb⟩ := hx
  obtain ⟨⟨hyn, hyo⟩, hyb⟩ := hy
  refine ⟨⟨fun i j => add_nonneg (hxn i j) (mul_nonneg hθ (hyn i j)),
    fun i j h => by simp [hxo i j h, hyo i j h]⟩, ?_⟩
  intro i
  have h1 := hxb i
  have h2 := hyb i
  simp only at h2 ⊢
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have : θ * (∑ j ∈ Finset.univ.filter (fun j => (j, i) ∈ G.A), y j i)
      - θ * (∑ k ∈ Finset.univ.filter (fun k => (i, k) ∈ G.A), y i k) = 0 := by
    rw [← mul_sub, h2, mul_zero]
  linarith

/-- The indicator of a simple circuit is a simple circulation with that support. -/
lemma circuit_indicator (G : ArcGraph n) (C : Finset (Fin n × Fin n)) (hC : IsSimpleCircuit G C) :
    IsSimpleCirculation G (fun i j => if (i, j) ∈ C then 1 else 0) ∧
      support G (fun i j => if (i, j) ∈ C then 1 else 0) = C := by
  obtain ⟨m, v, hv, hA, rfl⟩ := hC
  set C := Finset.univ.image (fun k => (v k, v (k + 1))) with hCdef
  have hCA : ∀ p ∈ C, p ∈ G.A := by
    intro p hp
    rw [hCdef, Finset.mem_image] at hp
    obtain ⟨k, _, rfl⟩ := hp
    exact hA k
  have hsupp : support G (fun i j => if (i, j) ∈ C then 1 else 0) = C := by
    unfold support
    ext p
    simp only [Finset.mem_filter, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
    exact ⟨fun h => h.2, fun h => ⟨hCA p h, h⟩⟩
  refine ⟨⟨⟨⟨fun i j => by dsimp only; split_ifs <;> norm_num, fun i j h => ?_⟩, ?_⟩, ?_⟩, hsupp⟩
  · dsimp only; rw [if_neg]; exact fun h' => h (hCA _ h')
  · intro i
    simp only
    rw [Finset.sum_boole, Finset.sum_boole, Finset.filter_filter, Finset.filter_filter]
    have hin : (Finset.univ.filter (fun j => (j, i) ∈ G.A ∧ (j, i) ∈ C)) =
        (Finset.univ.filter (fun k => v (k + 1) = i)).image v := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hCdef,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, k, h1, h2⟩
        exact ⟨k, h2, h1⟩
      · rintro ⟨k, h2, h1⟩
        refine ⟨?_, k, h1, h2⟩
        rw [← h1, ← h2]; exact hA k
    have hout : (Finset.univ.filter (fun j => (i, j) ∈ G.A ∧ (i, j) ∈ C)) =
        (Finset.univ.filter (fun k => v k = i)).image (fun k => v (k + 1)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hCdef,
        Prod.mk.injEq]
      constructor
      · rintro ⟨_, k, h1, h2⟩
        exact ⟨k, h1, h2⟩
      · rintro ⟨k, h1, h2⟩
        refine ⟨?_, k, h1, h2⟩
        rw [← h1, ← h2]; exact hA k
    have hshift : (Finset.univ.filter (fun k => v k = i)) =
        (Finset.univ.filter (fun k => v (k + 1) = i)).map (Equiv.addRight (1 : Fin (m + 2))).toEmbedding := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
        Equiv.coe_addRight]
      simp
    rw [hin, hout, Finset.card_image_of_injective _ hv,
      Finset.card_image_of_injective _
        (show Function.Injective (fun k : Fin (m + 2) => v (k + 1)) from
          hv.comp (add_left_injective 1)), hshift, Finset.card_map]
    simp
  · rw [hsupp]; exact ⟨m, v, hv, hA, rfl⟩

end SSThm1Aux

open SSThm1Aux

theorem solution {n : ℕ} (G : ArcGraph n) (c : Fin n → Fin n → ℝ → ℝ)
    (hc : IsConcaveArcCost G c) :
    List.TFAE
        [ ∃ (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r x,
          IsMinCostFlow G c (fun _ => 0) (fun _ _ => 0),
          ∀ r : Fin n → ℝ, (∃ x, IsFlow G r x) →
            ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x,
          ∀ y, IsSimpleCirculation G y → 0 ≤ flowCost G c y,
          ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2),
          ∀ S, IsSinkSelection G S → ∀ (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
            ∀ u, HasMinCostChain G S (augCost G c b bν) u ] ∧
      ∀ (r : Fin n → ℝ) (S : Finset (Fin n)) (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
        IsSinkSelection G S → (∃ x, IsFlow G r x) →
        (∀ p ∈ G.A, ¬ SameComponent G p.1 p.2 →
          b p.1 p.2 * (∑ i, max (r i) 0) ≤ c p.1 p.2 (∑ i, max (r i) 0)) →
        (((∃ (r' : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r' x) ↔
            ∃ π : Fin n → ℝ, ∀ p ∈ G.A, ∀ x, IsFlow G r x →
              0 ≤ reducedArcCost c π p.1 p.2 (x p.1 p.2)) ∧
          ((∃ (r' : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r' x) →
            (∀ i, minChainCost G S (augCost G c b bν) i ≠ ⊥ ∧
              minChainCost G S (augCost G c b bν) i ≠ ⊤) ∧
            ∀ p ∈ G.A, ∀ x, IsFlow G r x →
              0 ≤ reducedArcCost c (fun i => (minChainCost G S (augCost G c b bν) i).toReal)
                p.1 p.2 (x p.1 p.2))) := by
  have hHH := hirsch_hoffman_extension G c hc
  have h14 : (∃ (r : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r x) →
      ∀ y, IsSimpleCirculation G y → 0 ≤ flowCost G c y := by
    rintro ⟨r, x, hx⟩ y hy
    obtain ⟨hiff, hext⟩ := hHH r ⟨x, hx.1⟩
    obtain ⟨x', hx'm, hx'e⟩ := hext ⟨x, hx⟩
    obtain ⟨M, hM⟩ := hiff.mp ⟨x, hx⟩ x' hx'e y hy
    have hb : ∀ θ : ℝ, 0 ≤ θ → M - flowCost G c x' ≤ flowCost G c (fun i j => θ * y i j) := by
      intro θ hθ
      have := (concave_sandwich G c hc x' y hx'm.1.1 hy.1.1 θ hθ).2
      linarith [hM θ hθ]
    have := bounded_imp_nonneg G c hc y hy.1.1 _ hb 1 zero_le_one
    simpa using this
  have h43 : (∀ y, IsSimpleCirculation G y → 0 ≤ flowCost G c y) →
      ∀ r : Fin n → ℝ, (∃ x, IsFlow G r x) →
        ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x := by
    intro h4 r hr
    obtain ⟨hiff, hext⟩ := hHH r hr
    apply hext
    apply hiff.mpr
    intro x hx y hy
    refine ⟨(1 / 2 : ℝ) * flowCost G c (fun i j => 2 * x i j), fun θ hθ => ?_⟩
    have hs := (concave_sandwich G c hc x y hx.1.1 hy.1.1 θ hθ).1
    have : 0 ≤ flowCost G c (fun i j => 2 * (θ * y i j)) := by
      rcases hθ.eq_or_lt with h | h
      · subst h
        unfold flowCost
        apply Finset.sum_nonneg
        intro p hp
        simp [(hc p hp).2]
      · have := h4 _ (simple_scale G y hy (2 * θ) (by positivity))
        have e : (fun i j => 2 * (θ * y i j)) = (fun i j => 2 * θ * y i j) := by
          funext i j; ring
        rw [e]; exact this
    linarith
  have h32 : (∀ r : Fin n → ℝ, (∃ x, IsFlow G r x) →
        ∃ x, IsMinCostFlow G c r x ∧ IsExtremeFlow G r x) →
      IsMinCostFlow G c (fun _ => 0) (fun _ _ => 0) := by
    intro h3
    obtain ⟨x, hxm, hxe⟩ := h3 (fun _ => 0) ⟨_, zero_isFlow G⟩
    have := (extreme_circulation_iff_eq_zero G x hxm.1).mp hxe
    subst this
    exact hxm
  have h45 : (∀ y, IsSimpleCirculation G y → 0 ≤ flowCost G c y) →
      ∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2) := by
    intro h4 C hC
    obtain ⟨hy, hsupp⟩ := circuit_indicator G C hC
    rw [← hsupp]
    refine (simpleCirculation_cost_nonneg_iff G c hc _ hy).mp ?_
    intro θ hθ
    rcases hθ.eq_or_lt with h | h
    · subst h
      unfold flowCost
      apply Finset.sum_nonneg
      intro p hp
      simp [(hc p hp).2]
    · exact h4 _ (simple_scale G _ hy θ h)
  have h54 : (∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2)) →
      ∀ y, IsSimpleCirculation G y → 0 ≤ flowCost G c y := by
    intro h5 y hy
    have := (simpleCirculation_cost_nonneg_iff G c hc y hy).mpr (h5 _ hy.2) 1 zero_le_one
    simpa using this
  have h56 : (∀ C, IsSimpleCircuit G C → 0 ≤ ∑ p ∈ C, slopeAtInfty (c p.1 p.2)) →
      ∀ S, IsSinkSelection G S → ∀ (b : Fin n → Fin n → ℝ) (bν : Fin n → ℝ),
        ∀ u, HasMinCostChain G S (augCost G c b bν) u :=
    fun h5 S hS b bν u => five_implies_six G c h5 S hS b bν u
  have h65 := six_implies_five G c
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 4 := h14
    tfae_have 4 → 3 := h43
    tfae_have 3 → 2 := h32
    tfae_have 2 → 1 := fun h => ⟨_, _, h⟩
    tfae_have 4 → 5 := h45
    tfae_have 5 → 4 := h54
    tfae_have 5 → 6 := h56
    tfae_have 6 → 5 := h65
    tfae_finish
  · intro r S b bν hS hflow hext
    have key : (∃ (r' : Fin n → ℝ) (x : Fin n → Fin n → ℝ), IsMinCostFlow G c r' x) →
        (∀ i, minChainCost G S (augCost G c b bν) i ≠ ⊥ ∧
          minChainCost G S (augCost G c b bν) i ≠ ⊤) ∧
        ∀ p ∈ G.A, ∀ x, IsFlow G r x →
          0 ≤ reducedArcCost c (fun i => (minChainCost G S (augCost G c b bν) i).toReal)
            p.1 p.2 (x p.1 p.2) := by
      intro h1
      obtain ⟨hA, hR, hT⟩ := six_implies_seven_bounds G c hc r S hS b bν hext
        (h56 (h45 (h14 h1)) S hS b bν)
      refine ⟨hR, fun p hp x hx => ?_⟩
      have h1' := hA x hx p hp
      have h2' := hT p hp
      obtain ⟨hb1, ht1⟩ := hR p.1
      obtain ⟨hb2, ht2⟩ := hR p.2
      have hx0 : 0 ≤ x p.1 p.2 := hx.1.1 _ _
      have hc0 : c p.1 p.2 0 = 0 := (hc p hp).2
      simp only [reducedArcCost]
      rw [← EReal.coe_toReal ht1 hb1, ← EReal.coe_toReal ht2 hb2] at h2'
      generalize (minChainCost G S (augCost G c b bν) p.1).toReal = a at h2' ⊢
      generalize (minChainCost G S (augCost G c b bν) p.2).toReal = a' at h2' ⊢
      generalize augCost G c b bν (some p.1) (some p.2) = A at h1' h2'
      generalize x p.1 p.2 = t at h1' hx0 ⊢
      induction A using EReal.rec with
      | bot => simp at h2'
      | top =>
        rcases hx0.eq_or_lt with h | h
        · subst h; simp [hc0]
        · rw [EReal.top_mul_of_pos (by exact_mod_cast h)] at h1'
          simp at h1'
      | coe α =>
        have e1 : a ≤ α + a' := by exact_mod_cast h2'
        have e2 : α * t ≤ c p.1 p.2 t := by exact_mod_cast h1'
        nlinarith [mul_nonneg (show 0 ≤ α + a' - a by linarith) hx0]
    refine ⟨⟨fun h1 => ⟨_, (key h1).2⟩, ?_⟩, key⟩
    rintro ⟨π, hπ⟩
    obtain ⟨hiff, -⟩ := hHH r hflow
    obtain ⟨x0, hx0⟩ := hiff.mpr (by
      intro x hx y hy
      refine ⟨-(∑ i, π i * r i), fun θ hθ => ?_⟩
      have hxy := flow_add_circ G r x y hx.1 hy.1 θ hθ
      have e := reducedFlowCost_eq G c π r _ hxy
      have hnn : 0 ≤ reducedFlowCost G c π (fun i j => x i j + θ * y i j) :=
        Finset.sum_nonneg (fun p hp => hπ p hp _ hxy)
      linarith)
    exact ⟨r, x0, hx0⟩
