-- Prove2me | solution 1 for SubadditiveMMS580.Amplification.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:41:49.514205+00:00
-- url     : https://prove2.me/submissions/d052aa7c-5854-41bc-a150-a4deb3c6038b

import Mathlib
import Definitions.Def_SubadditiveMMS580_Amplification_Setting
import Definitions.Def_MultiAllocToAlloc_Subadditive_Valuation
import Definitions.Def_SubmodOrder_Subadditive
import Theorems.Thm_SubadditiveMMS580_Amplification_lemma_3_1
import Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
section
set_option autoImplicit false

namespace SubadditiveMMS580.Amplification.Dev.FD

open SubadditiveMMS580.Amplification

/-- Push a finitely supported distribution forward along a map. -/
noncomputable def map {α β : Type*} [DecidableEq β] (σ : FinDist α) (f : α → β) : FinDist β where
  support := σ.support.image f
  weight := fun y => ∑ x ∈ σ.support.filter (fun x => f x = y), σ.weight x
  weight_pos := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    refine Finset.sum_pos (fun x hx => σ.weight_pos x (Finset.mem_filter.1 hx).1) ⟨x, ?_⟩
    simp [hx]
  sum_weight := by
    rw [Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
    exact σ.sum_weight

theorem prob_map {α β : Type*} [DecidableEq β] (σ : FinDist α) (f : α → β) (E : β → Prop) :
    (map σ f).prob E = σ.prob (fun x => E (f x)) := by
  classical
  unfold FinDist.prob
  show ∑ y ∈ (σ.support.image f).filter E,
      ∑ x ∈ σ.support.filter (fun x => f x = y), σ.weight x = _
  have h1 : ∀ y ∈ (σ.support.image f).filter E,
      ∑ x ∈ σ.support.filter (fun x => f x = y), σ.weight x =
      ∑ x ∈ (σ.support.filter (fun x => E (f x))).filter (fun x => f x = y), σ.weight x := by
    intro y hy
    have hEy := (Finset.mem_filter.1 hy).2
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hxy⟩; exact ⟨⟨hx, hxy ▸ hEy⟩, hxy⟩
    · rintro ⟨⟨hx, _⟩, hxy⟩; exact ⟨hx, hxy⟩
  rw [Finset.sum_congr rfl h1]
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_image_of_mem f hx.1, hx.2⟩) _

/-- The distribution with weights given by a point of the standard simplex. -/
noncomputable def ofSimplex {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : p ∈ stdSimplex ℝ ι) :
    FinDist ι where
  support := Finset.univ.filter (fun i => 0 < p i)
  weight := p
  weight_pos := by intro x hx; simpa using hx
  sum_weight := by
    rw [Finset.sum_filter_of_ne (fun i _ hne => lt_of_le_of_ne (hp.1 i) (Ne.symm hne))]
    exact hp.2

end SubadditiveMMS580.Amplification.Dev.FD
end

section
set_option autoImplicit false

namespace SubadditiveMMS580.Amplification.Dev.FD

open SubadditiveMMS580.Amplification

/-- Expectation of a real function under a finitely supported distribution. -/
noncomputable def expect {α : Type*} (σ : FinDist α) (G : α → ℝ) : ℝ :=
  ∑ x ∈ σ.support, σ.weight x * G x

open Classical in
theorem prob_eq_expect {α : Type*} (σ : FinDist α) (E : α → Prop) :
    σ.prob E = expect σ (fun x => if E x then 1 else 0) := by
  unfold FinDist.prob expect
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun x _ => by split_ifs with h <;> simp [h])

theorem expect_mono {α : Type*} (σ : FinDist α) {G H : α → ℝ}
    (h : ∀ x ∈ σ.support, G x ≤ H x) : expect σ G ≤ expect σ H :=
  Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left (h x hx) (σ.weight_pos x hx).le)

theorem expect_const {α : Type*} (σ : FinDist α) (c : ℝ) : expect σ (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, σ.sum_weight, one_mul]

theorem expect_const_mul {α : Type*} (σ : FinDist α) (c : ℝ) (G : α → ℝ) :
    expect σ (fun x => c * G x) = c * expect σ G := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => by ring)

theorem expect_sum {α ι : Type*} (σ : FinDist α) (s : Finset ι) (G : ι → α → ℝ) :
    expect σ (fun x => ∑ i ∈ s, G i x) = ∑ i ∈ s, expect σ (G i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Dependent pairing: draw `a ∼ σ`, then `b ∼ κ a`. -/
noncomputable def bind {α β : Type*} [DecidableEq α] [DecidableEq β] (σ : FinDist α)
    (κ : α → FinDist β) : FinDist (Σ _ : α, β) where
  support := σ.support.sigma (fun a => (κ a).support)
  weight := fun p => σ.weight p.1 * (κ p.1).weight p.2
  weight_pos := by
    rintro ⟨a, b⟩ h
    rw [Finset.mem_sigma] at h
    exact mul_pos (σ.weight_pos a h.1) ((κ a).weight_pos b h.2)
  sum_weight := by
    rw [Finset.sum_sigma]
    simp only
    have : ∀ a ∈ σ.support, ∑ b ∈ (κ a).support, σ.weight a * (κ a).weight b = σ.weight a := by
      intro a _
      rw [← Finset.mul_sum, (κ a).sum_weight, mul_one]
    rw [Finset.sum_congr rfl this]
    exact σ.sum_weight

theorem expect_bind {α β : Type*} [DecidableEq α] [DecidableEq β] (σ : FinDist α)
    (κ : α → FinDist β) (G : (Σ _ : α, β) → ℝ) :
    expect (bind σ κ) G = ∑ a ∈ σ.support, σ.weight a * expect (κ a) (fun b => G ⟨a, b⟩) := by
  unfold expect
  show ∑ p ∈ σ.support.sigma (fun a => (κ a).support), σ.weight p.1 * (κ p.1).weight p.2 * G p = _
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun b _ => by ring)

section Pi

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j, DecidableEq (X j)]

/-- Product of a family of finitely supported distributions. -/
noncomputable def pi (μ : ∀ j, FinDist (X j)) : FinDist (∀ j, X j) where
  support := Fintype.piFinset (fun j => (μ j).support)
  weight := fun ω => ∏ j, (μ j).weight (ω j)
  weight_pos := by
    intro ω h
    rw [Fintype.mem_piFinset] at h
    exact Finset.prod_pos (fun j _ => (μ j).weight_pos _ (h j))
  sum_weight := by
    rw [← Finset.prod_univ_sum (fun j => (μ j).support) (fun j x => (μ j).weight x)]
    exact Finset.prod_eq_one (fun j _ => (μ j).sum_weight)

theorem mem_support_pi (μ : ∀ j, FinDist (X j)) (ω : ∀ j, X j) :
    ω ∈ (pi μ).support ↔ ∀ j, ω j ∈ (μ j).support := Fintype.mem_piFinset

/-- The weight of all coordinates except `j0`. -/
noncomputable def rest (μ : ∀ j, FinDist (X j)) (j0 : J) (ω : ∀ j, X j) : ℝ :=
  ∏ j ∈ Finset.univ.erase j0, (μ j).weight (ω j)

theorem pi_weight_eq (μ : ∀ j, FinDist (X j)) (j0 : J) (ω : ∀ j, X j) :
    (pi μ).weight ω = (μ j0).weight (ω j0) * rest μ j0 ω := by
  show ∏ j, (μ j).weight (ω j) = _
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j0)]
  rfl

theorem rest_update (μ : ∀ j, FinDist (X j)) (j0 : J) (ω : ∀ j, X j) (x : X j0) :
    rest μ j0 (Function.update ω j0 x) = rest μ j0 ω := by
  unfold rest
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem update_mem_support (μ : ∀ j, FinDist (X j)) (j0 : J) {ω : ∀ j, X j}
    (hω : ω ∈ (pi μ).support) {x : X j0} (hx : x ∈ (μ j0).support) :
    Function.update ω j0 x ∈ (pi μ).support := by
  rw [mem_support_pi] at hω ⊢
  intro j
  by_cases h : j = j0
  · subst h; simpa using hx
  · rw [Function.update_of_ne h]; exact hω j

/-- Fibre sum of the rest-weighted `G ∘ update`. -/
noncomputable def fib (μ : ∀ j, FinDist (X j)) (j0 : J) (G : (∀ j, X j) → ℝ) (y x : X j0) : ℝ :=
  ∑ ω ∈ (pi μ).support.filter (fun ω => ω j0 = y),
    rest μ j0 ω * G (Function.update ω j0 x)

theorem fib_eq (μ : ∀ j, FinDist (X j)) (j0 : J) (G : (∀ j, X j) → ℝ) {y x : X j0}
    (hy : y ∈ (μ j0).support) (hx : x ∈ (μ j0).support) :
    fib μ j0 G y x = fib μ j0 G x x := by
  unfold fib
  refine Finset.sum_nbij' (fun ω => Function.update ω j0 x) (fun ω => Function.update ω j0 y)
    ?_ ?_ ?_ ?_ ?_
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨update_mem_support μ j0 hω.1 hx, by simp⟩
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨update_mem_support μ j0 hω.1 hy, by simp⟩
  · intro ω hω
    rw [Finset.mem_filter] at hω
    simp [← hω.2]
  · intro ω hω
    rw [Finset.mem_filter] at hω
    simp [← hω.2]
  · intro ω _
    rw [rest_update, Function.update_idem]

theorem expect_pi_resample (μ : ∀ j, FinDist (X j)) (j0 : J) (G : (∀ j, X j) → ℝ) :
    expect (pi μ) G
      = expect (pi μ) (fun ω => expect (μ j0) (fun x => G (Function.update ω j0 x))) := by
  -- K x = ∑ over the fibre {ω j0 = x} of rest * G
  have hfib : ∀ y ∈ (μ j0).support, ∀ x ∈ (μ j0).support,
      ∑ ω ∈ (pi μ).support, (pi μ).weight ω * G (Function.update ω j0 x) *
        (if ω j0 = y then 1 else 0) = (μ j0).weight y * fib μ j0 G x x := by
    intro y hy x hx
    rw [← fib_eq μ j0 G hy hx, fib, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases h : ω j0 = y
    · simp only [h, if_true, mul_one]
      rw [pi_weight_eq μ j0, h]; ring
    · simp [h]
  have hfiber : ∀ H : (∀ j, X j) → ℝ,
      ∑ ω ∈ (pi μ).support, H ω
        = ∑ y ∈ (μ j0).support, ∑ ω ∈ (pi μ).support, H ω * (if ω j0 = y then 1 else 0) := by
    intro H
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ω hω => ?_)
    rw [← Finset.mul_sum, Finset.sum_ite_eq]
    rw [if_pos ((mem_support_pi μ ω).1 hω j0), mul_one]
  have hL : expect (pi μ) G = ∑ x ∈ (μ j0).support, (μ j0).weight x * fib μ j0 G x x := by
    have := hfiber (fun ω => (pi μ).weight ω * G ω)
    unfold expect
    rw [this]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have h2 := hfib x hx x hx
    rw [← h2]
    refine Finset.sum_congr rfl (fun ω hω => ?_)
    by_cases h : ω j0 = x
    · subst h; simp
    · simp [h]
  rw [hL]
  conv_rhs => unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have h1 := hfiber (fun ω => (pi μ).weight ω * G (Function.update ω j0 x))
  have h3 : ∑ y ∈ (μ j0).support, (μ j0).weight y * fib μ j0 G x x
      = fib μ j0 G x x := by
    rw [← Finset.sum_mul, (μ j0).sum_weight, one_mul]
  have h4 : ∑ ω ∈ (pi μ).support, (pi μ).weight ω * G (Function.update ω j0 x)
      = fib μ j0 G x x := by
    rw [h1, ← h3]
    exact Finset.sum_congr rfl (fun y hy => hfib y hy x hx)
  rw [← h4, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

theorem expect_pi_resample_mul (μ : ∀ j, FinDist (X j)) (j0 : J) (g : (∀ j, X j) → ℝ)
    (F : (∀ j, X j) → X j0 → ℝ) (q : ℝ)
    (hg : ∀ ω x, g (Function.update ω j0 x) = g ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hF : ∀ ω x, 0 ≤ F ω x)
    (hF' : ∀ ω x, F (Function.update ω j0 x) x = F ω x)
    (hq : ∀ ω, expect (μ j0) (fun x => F ω x) ≤ q) :
    expect (pi μ) (fun ω => g ω * F ω (ω j0)) ≤ q * expect (pi μ) g := by
  rw [expect_pi_resample μ j0]
  have h1 : ∀ ω, expect (μ j0) (fun x => g (Function.update ω j0 x) *
      F (Function.update ω j0 x) (Function.update ω j0 x j0)) = g ω * expect (μ j0) (F ω) := by
    intro ω
    rw [← expect_const_mul]
    unfold expect
    refine Finset.sum_congr rfl (fun x _ => ?_)
    dsimp only
    rw [hg, Function.update_self, hF']
  simp_rw [h1]
  rw [← expect_const_mul]
  exact expect_mono _ (fun ω _ => by
    rw [mul_comm q]
    exact mul_le_mul_of_nonneg_left (hq ω) (hg0 ω))

end Pi

end SubadditiveMMS580.Amplification.Dev.FD
end

section
set_option autoImplicit false

namespace SubadditiveMMS580.Amplification.Dev.Bid

open SubadditiveMMS580.Amplification

noncomputable def emb {m : ℕ} (P : Finset (Fin m)) : Fin P.card ↪ Fin m :=
  ⟨fun a => (P.equivFin.symm a).1, fun _ _ h => P.equivFin.symm.injective (Subtype.ext h)⟩

theorem emb_apply {m : ℕ} (P : Finset (Fin m)) (a : Fin P.card) :
    emb P a = (P.equivFin.symm a).1 := rfl

theorem range_emb {m : ℕ} (P : Finset (Fin m)) : P = Finset.univ.map (emb P) := by
  ext g
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hg
    exact ⟨P.equivFin ⟨g, hg⟩, by rw [emb_apply]; simp⟩
  · rintro ⟨a, rfl⟩
    exact (P.equivFin.symm a).2

noncomputable def ext {m : ℕ} (P : Finset (Fin m)) (b : Fin P.card → ℝ) : Fin m → ℝ :=
  fun g => if h : g ∈ P then b (P.equivFin ⟨g, h⟩) else 0

theorem ext_emb {m : ℕ} (P : Finset (Fin m)) (b : Fin P.card → ℝ) (a : Fin P.card) :
    ext P b (emb P a) = b a := by
  have h : emb P a ∈ P := (P.equivFin.symm a).2
  unfold ext
  rw [dif_pos h]
  have : (⟨emb P a, h⟩ : P) = P.equivFin.symm a := rfl
  rw [this, Equiv.apply_symm_apply]

theorem exists_bid_dist {m : ℕ} (v : Finset (Fin m) → ℝ)
    (hnorm : MultiAllocToAlloc.Subadditive.IsNormalized v)
    (hmono : MultiAllocToAlloc.Subadditive.IsMonotone v)
    (hsub : SubmodOrder.Subadditive v)
    (P : Finset (Fin m)) (hP : P.Nonempty) (B : ℝ) (hB : 0 < B) :
    ∃ τ : SubadditiveMMS580.Amplification.FinDist (Fin m → ℝ),
      (∀ b ∈ τ.support, (∀ g, 0 ≤ b g) ∧ (∀ g, g ∉ P → b g = 0) ∧ ∑ g, b g ≤ B) ∧
      ∀ c : Fin m → ℝ, (∀ g, 0 ≤ c g) → ∑ g ∈ P, c g ≤ B / 2 →
        (1 : ℝ) / 2 ≤ τ.prob (fun b => v P / 2 ≤ v (P.filter (fun g => c g < b g))) := by
  classical
  have hs : 0 < P.card := Finset.card_pos.2 hP
  let v' : Finset (Fin P.card) → ℝ := fun T => v (T.map (emb P))
  have hn' : MultiAllocToAlloc.Subadditive.IsNormalized v' := by
    unfold MultiAllocToAlloc.Subadditive.IsNormalized at hnorm ⊢
    simpa [v'] using hnorm
  have hm' : MultiAllocToAlloc.Subadditive.IsMonotone v' := fun S T hST =>
    hmono _ _ (Finset.map_subset_map.2 hST)
  have hsub' : SubmodOrder.Subadditive v' := fun A B' => by
    simpa [v', Finset.map_union] using hsub (A.map (emb P)) (B'.map (emb P))
  obtain ⟨σ, hσ1, hσ2⟩ := SubadditiveMMS580.Amplification.lemma_3_1 P.card hs v' hn' hm' hsub' B hB
  have hsum : ∀ f : Fin m → ℝ, (∀ g, g ∉ P → f g = 0) →
      ∑ g, f g = ∑ a : Fin P.card, f (emb P a) := by
    intro f hf
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun g _ hg => hf g hg)]
    have h := Finset.sum_map (Finset.univ : Finset (Fin P.card)) (emb P) f
    rw [← range_emb P] at h
    exact h
  refine ⟨FD.map σ (ext P), ?_, ?_⟩
  · intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := hσ1 b0 hb0
    have hoff : ∀ g, g ∉ P → ext P b0 g = 0 := fun g hg => by simp [ext, hg]
    refine ⟨fun g => ?_, hoff, ?_⟩
    · unfold ext; split_ifs
      · exact h1 _
      · exact le_rfl
    · rw [hsum _ hoff]
      simpa [ext_emb] using h2
  · intro c hc hcs
    have h := hσ2 (fun a => c (emb P a)) (fun a => hc _) (by
      have h := Finset.sum_map (Finset.univ : Finset (Fin P.card)) (emb P) c
      rw [← range_emb P] at h
      exact h ▸ hcs)
    rw [FD.prob_map]
    convert h using 2
    funext b
    have e1 : v' Finset.univ = v P := by
      simp only [v']; rw [← range_emb P]
    have e2 : v' (Finset.univ.filter (fun a => c (emb P a) < b a)) =
        v (P.filter (fun g => c g < ext P b g)) := by
      simp only [v']
      congr 1
      ext g
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨(P.equivFin.symm a).2, ?_⟩
        rw [ext_emb]; exact ha
      · rintro ⟨hg, hlt⟩
        obtain ⟨a, rfl⟩ : ∃ a, emb P a = g := by
          have := range_emb P ▸ hg
          simpa using this
        exact ⟨a, by rwa [ext_emb] at hlt, rfl⟩
    rw [e1, e2]

end SubadditiveMMS580.Amplification.Dev.Bid
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.T14

open SubadditiveMMS580.Amplification.Dev.FD

/-- uniform distribution on `Fin n` -/
noncomputable def unif (n : ℕ) (hn : 1 ≤ n) : FinDist (Fin n) :=
  ofSimplex (fun _ => 1 / (n : ℝ)) ⟨fun _ => by positivity, by
    have : (n : ℝ) ≠ 0 := by positivity
    simp [Finset.sum_const]; field_simp⟩

theorem unif_support (n : ℕ) (hn : 1 ≤ n) : (unif n hn).support = Finset.univ := by
  ext r
  simp only [unif, ofSimplex, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  positivity

theorem expect_one_sub {α : Type*} (σ : FinDist α) (G : α → ℝ) :
    expect σ (fun x => 1 - G x) = 1 - expect σ G := by
  unfold expect
  have : ∀ x ∈ σ.support, σ.weight x * (1 - G x) = σ.weight x - σ.weight x * G x :=
    fun x _ => by ring
  rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, σ.sum_weight]

theorem unif_weight (n : ℕ) (hn : 1 ≤ n) (r : Fin n) : (unif n hn).weight r = 1 / (n : ℝ) := rfl

theorem success_bound {m n : ℕ} (hn : 1 ≤ n) (u ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (v : Finset (Fin m) → ℝ) (hmono : IsMonotone v)
    (W : Fin n → Finset (Fin m)) (hW : IsValuableFamily v W)
    (τ : Fin n → FinDist (Fin m → ℝ))
    (hτ2 : ∀ r (c : Fin m → ℝ), (∀ g, 0 ≤ c g) → ∑ g ∈ W r, c g ≤ ((1 : ℝ) / ℓ) / 2 →
      (1 : ℝ) / 2 ≤ (τ r).prob (fun b => v (W r) / 2 ≤ v ((W r).filter (fun g => c g < b g))))
    (c : Fin m → ℝ) (hc0 : ∀ g, 0 ≤ c g) (hcs : ∑ g, c g ≤ (u : ℝ) - 1) :
    expect (bind (unif n hn) τ) (fun x =>
      if (1 : ℝ) / 2 ≤ v (Finset.univ.filter (fun g => c g < x.2 g)) then 0 else 1) ≤
      1 / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / n := by
  classical
  set t : ℝ := ((1 : ℝ) / ℓ) / 2 with ht
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htpos : 0 < t := by positivity
  rw [expect_bind, unif_support]
  set bad : Finset (Fin n) := Finset.univ.filter (fun r => t < ∑ g ∈ W r, c g) with hbad
  have he : ∀ r : Fin n, expect (τ r) (fun b =>
      if (1 : ℝ) / 2 ≤ v (Finset.univ.filter (fun g => c g < (⟨r, b⟩ : (Σ _ : Fin n, Fin m → ℝ)).2 g))
        then 0 else 1) ≤ 1 / 2 + (if r ∈ bad then 1 / 2 else 0) := by
    intro r
    by_cases hr : r ∈ bad
    · rw [if_pos hr]
      calc _ ≤ expect (τ r) (fun _ => (1 : ℝ)) :=
            expect_mono _ (fun b _ => by dsimp only; split_ifs <;> norm_num)
        _ = 1 := expect_const _ _
        _ = 1 / 2 + 1 / 2 := by norm_num
    · rw [if_neg hr, add_zero]
      have hgood : ∑ g ∈ W r, c g ≤ t := by
        by_contra h; exact hr (by simp [hbad]; linarith)
      have hp := hτ2 r c hc0 hgood
      rw [prob_eq_expect] at hp
      calc _ ≤ expect (τ r) (fun b => 1 - (if v (W r) / 2 ≤ v ((W r).filter (fun g => c g < b g))
              then (1 : ℝ) else 0)) := by
            apply expect_mono
            intro b _
            dsimp only
            by_cases hE : v (W r) / 2 ≤ v ((W r).filter (fun g => c g < b g))
            · have hS : (1 : ℝ) / 2 ≤ v (Finset.univ.filter (fun g => c g < b g)) := by
                have h1 := hmono ((W r).filter (fun g => c g < b g))
                  (Finset.univ.filter (fun g => c g < b g)) (by
                    intro g hg
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
                    exact hg.2)
                have := hW.2 r
                linarith
              rw [if_pos hS, if_pos hE]; norm_num
            · rw [if_neg hE]; split_ifs <;> norm_num
        _ = 1 - expect (τ r) (fun b => if v (W r) / 2 ≤ v ((W r).filter (fun g => c g < b g))
              then (1 : ℝ) else 0) := by
            exact expect_one_sub _ _
        _ ≤ 1 / 2 := by linarith
  -- counting bad sets
  have hbadcard : (bad.card : ℝ) * t ≤ (u : ℝ) - 1 := by
    have h1 : (bad.card : ℝ) * t ≤ ∑ r ∈ bad, ∑ g ∈ W r, c g := by
      have := Finset.card_nsmul_le_sum bad (fun r => ∑ g ∈ W r, c g) t
        (fun r hr => (by simpa [hbad] using hr : t < _).le)
      simpa [nsmul_eq_mul] using this
    have h2 : ∑ r ∈ bad, ∑ g ∈ W r, c g ≤ ∑ r, ∑ g ∈ W r, c g :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun r _ _ => Finset.sum_nonneg (fun g _ => hc0 g))
    have h3 : ∑ r, ∑ g ∈ W r, c g = ∑ g ∈ Finset.univ.biUnion W, c g := by
      rw [Finset.sum_biUnion]
      intro r _ s _ hrs
      exact hW.1 r s hrs
    have h4 : ∑ g ∈ Finset.univ.biUnion W, c g ≤ ∑ g, c g :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun g _ _ => hc0 g)
    linarith
  have hbad2 : (bad.card : ℝ) ≤ 2 * ℓ * ((u : ℝ) - 1) := by
    have : t = 1 / (2 * ℓ) := by rw [ht]; field_simp
    rw [this] at hbadcard
    have h5 : (bad.card : ℝ) * (1 / (2 * ℓ)) * (2 * ℓ) ≤ ((u : ℝ) - 1) * (2 * ℓ) :=
      mul_le_mul_of_nonneg_right hbadcard (by positivity)
    have h6 : (bad.card : ℝ) * (1 / (2 * ℓ)) * (2 * ℓ) = bad.card := by field_simp
    nlinarith
  calc _ ≤ ∑ r : Fin n, 1 / (n : ℝ) * (1 / 2 + (if r ∈ bad then 1 / 2 else 0)) := by
        apply Finset.sum_le_sum
        intro r _
        rw [unif_weight]
        exact mul_le_mul_of_nonneg_left (he r) (by positivity)
    _ = 1 / 2 + (bad.card : ℝ) / (2 * n) := by
        have hs : ∑ r : Fin n, (if r ∈ bad then (1 / 2 : ℝ) else 0) = bad.card / 2 := by
          rw [Finset.sum_ite_mem, Finset.univ_inter]; simp; ring
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hs]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
    _ ≤ 1 / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / n := by
        have : (bad.card : ℝ) / (2 * n) ≤ (ℓ : ℝ) * ((u : ℝ) - 1) / n := by
          rw [div_le_div_iff₀ (by positivity) hnR]
          nlinarith
        linarith

end SubadditiveMMS580.Amplification.Dev.T14
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification.Dev.T14

open SubadditiveMMS580.Amplification.Dev.FD SubadditiveMMS580.Amplification.Dev.Bid

abbrev Xt (n m : ℕ) : Type := Σ _ : Fin n, (Fin m → ℝ)

theorem part1_core (u n : ℕ) (hu : 2 ≤ u) (hn : 1 ≤ n) {m : ℕ}
    (v : Fin u → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin u → Fin n → Finset (Fin m)) (hW : ∀ i, IsValuableFamily (v i) (W i))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ σ : FinDist (Fin u → Finset (Fin m)),
      (∀ A ∈ σ.support, IsAllocation A) ∧
      ∀ i : Fin u, σ.prob (fun A => v i (A i) < 1 / 2) ≤
        ((1 : ℝ) / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / (n : ℝ)) ^ ℓ := by
  classical
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (by omega : 1 ≤ u)
  have hWne : ∀ i r, (W i r).Nonempty := by
    intro i r
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := (hW i).2 r
    rw [h, hnorm i] at this
    linarith
  choose τ hτ using fun i r => exists_bid_dist (v i) (hnorm i) (hmono i) (hsub i) (W i r)
    (hWne i r) (1 / (ℓ : ℝ)) (by positivity)
  let μ : Fin u → FinDist (Xt n m) := fun i => bind (unif n hn) (τ i)
  let P : FinDist (Fin u × Fin ℓ → Xt n m) := pi (fun j : Fin u × Fin ℓ => μ j.1)
  let tot : (Fin u × Fin ℓ → Xt n m) → Fin u → Fin m → ℝ :=
    fun ω j g => ∑ t, (ω (j, t)).2 g
  let alloc : (Fin u × Fin ℓ → Xt n m) → Fin u → Finset (Fin m) :=
    fun ω i => Finset.univ.filter (fun g => ∀ j, j ≠ i → tot ω j g < tot ω i g)
  let cvec : (Fin u × Fin ℓ → Xt n m) → Fin u → Fin m → ℝ :=
    fun ω i g => ∑ j ∈ Finset.univ.erase i, tot ω j g
  -- support facts
  have hsupp : ∀ ω ∈ P.support, ∀ j t, (∀ g, 0 ≤ (ω (j, t)).2 g) ∧
      ∑ g, (ω (j, t)).2 g ≤ 1 / (ℓ : ℝ) := by
    intro ω hω j t
    have h1 := (mem_support_pi _ ω).1 hω (j, t)
    have h2 : ω (j, t) ∈ (μ j).support := h1
    have h3 := Finset.mem_sigma.1 h2
    have h4 := (hτ j (ω (j, t)).1).1 _ h3.2
    exact ⟨h4.1, h4.2.2⟩
  have htot0 : ∀ ω ∈ P.support, ∀ j g, 0 ≤ tot ω j g := fun ω hω j g =>
    Finset.sum_nonneg (fun t _ => (hsupp ω hω j t).1 g)
  have htot1 : ∀ ω ∈ P.support, ∀ j, ∑ g, tot ω j g ≤ 1 := by
    intro ω hω j
    show ∑ g, ∑ t, (ω (j, t)).2 g ≤ 1
    rw [Finset.sum_comm]
    calc ∑ t, ∑ g, (ω (j, t)).2 g ≤ ∑ _t : Fin ℓ, 1 / (ℓ : ℝ) :=
          Finset.sum_le_sum (fun t _ => (hsupp ω hω j t).2)
      _ = 1 := by simp; field_simp
  let goodc : (Fin u × Fin ℓ → Xt n m) → Fin u → Prop := fun ω i =>
    (∀ g, 0 ≤ cvec ω i g) ∧ ∑ g, cvec ω i g ≤ (u : ℝ) - 1
  have hgood : ∀ ω ∈ P.support, ∀ i, goodc ω i := by
    intro ω hω i
    refine ⟨fun g => Finset.sum_nonneg (fun j _ => htot0 ω hω j g), ?_⟩
    show ∑ g, ∑ j ∈ Finset.univ.erase i, tot ω j g ≤ _
    rw [Finset.sum_comm]
    calc ∑ j ∈ Finset.univ.erase i, ∑ g, tot ω j g ≤ ∑ _j ∈ Finset.univ.erase i, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => htot1 ω hω j)
      _ = (u : ℝ) - 1 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _)]
          simp [Nat.cast_sub (by omega : 1 ≤ u)]
  -- invariance of cvec
  have hcv : ∀ ω i t0 (x : Xt n m), cvec (Function.update ω (i, t0) x) i = cvec ω i := by
    intro ω i t0 x
    funext g
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine Finset.sum_congr rfl (fun t _ => ?_)
    have : (j, t) ≠ (i, t0) := fun h => (Finset.ne_of_mem_erase hj) (by simpa using congrArg Prod.fst h)
    rw [Function.update_of_ne this]
  let q : ℝ := 1 / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / n
  have hq0 : 0 ≤ q := by
    have : 0 ≤ (ℓ : ℝ) * ((u : ℝ) - 1) / n := by
      apply div_nonneg _ hnR.le
      exact mul_nonneg hℓR.le (by linarith)
    show 0 ≤ 1 / 2 + _
    linarith
  let S : (Fin u × Fin ℓ → Xt n m) → Fin u → Xt n m → Prop := fun ω i x =>
    (1 : ℝ) / 2 ≤ v i (Finset.univ.filter (fun g => cvec ω i g < x.2 g))
  let F : Fin u → (Fin u × Fin ℓ → Xt n m) → Xt n m → ℝ := fun i ω x =>
    if goodc ω i ∧ ¬ S ω i x then 1 else 0
  have hF0 : ∀ i ω x, 0 ≤ F i ω x := fun i ω x => by
    show 0 ≤ (if _ then (1 : ℝ) else 0); split_ifs <;> norm_num
  have hFinv : ∀ i t0 ω x y, F i (Function.update ω (i, t0) x) y = F i ω y := by
    intro i t0 ω x y
    simp only [F, goodc, S, hcv]
  have hFq : ∀ i ω, expect (μ i) (F i ω) ≤ q := by
    intro i ω
    by_cases hg : goodc ω i
    · have := success_bound hn u ℓ hℓ (v i) (hmono i) (W i) (hW i) (τ i)
        (fun r c hc hcs => (hτ i r).2 c hc hcs) (cvec ω i) hg.1 hg.2
      refine le_trans (le_of_eq ?_) this
      show expect (μ i) (F i ω) = _
      congr 1
      funext x
      show (if goodc ω i ∧ ¬ S ω i x then (1 : ℝ) else 0) = if S ω i x then 0 else 1
      by_cases h : S ω i x
      · rw [if_pos h, if_neg (fun hh => hh.2 h)]
      · rw [if_neg h, if_pos ⟨hg, h⟩]
    · have : F i ω = fun _ => 0 := by funext x; simp [F, hg]
      rw [this, expect_const]; exact hq0
  let G : Fin u → ℕ → (Fin u × Fin ℓ → Xt n m) → ℝ := fun i k ω =>
    ∏ t ∈ Finset.univ.filter (fun t : Fin ℓ => t.val < k), F i ω (ω (i, t))
  have hG : ∀ i k, k ≤ ℓ → expect P (G i k) ≤ q ^ k := by
    intro i k
    induction k with
    | zero =>
      intro _
      have : G i 0 = fun _ => 1 := by funext ω; simp [G]
      rw [this, expect_const]; simp
    | succ k ih =>
      intro hk
      let t0 : Fin ℓ := ⟨k, by omega⟩
      have hsplit : ∀ ω, G i (k + 1) ω = G i k ω * F i ω (ω (i, t0)) := by
        intro ω
        have : Finset.univ.filter (fun t : Fin ℓ => t.val < k + 1) =
            insert t0 (Finset.univ.filter (fun t : Fin ℓ => t.val < k)) := by
          ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro h
            by_cases h' : t.val < k
            · exact Or.inr h'
            · left; exact Fin.ext (by simp [t0]; omega)
          · rintro (rfl | h)
            · simp [t0]
            · omega
        simp only [G]
        rw [this, Finset.prod_insert (by simp [t0]), mul_comm]
      have hgi : ∀ ω x, G i k (Function.update ω (i, t0) x) = G i k ω := by
        intro ω x
        simp only [G]
        refine Finset.prod_congr rfl (fun t ht => ?_)
        have hne : (i, t) ≠ (i, t0) := by
          intro h
          have := congrArg Prod.snd h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          have : t = t0 := this
          rw [this] at ht
          simp [t0] at ht
        rw [Function.update_of_ne hne, hFinv]
      have hg0 : ∀ ω, 0 ≤ G i k ω := fun ω => Finset.prod_nonneg (fun t _ => hF0 _ _ _)
      have key := expect_pi_resample_mul (fun j : Fin u × Fin ℓ => μ j.1) (i, t0) (G i k)
        (fun ω x => F i ω x) q hgi hg0 (fun ω x => hF0 i ω x)
        (fun ω x => hFinv i t0 ω x x) (fun ω => hFq i ω)
      have h2 : expect P (G i (k + 1)) = expect P (fun ω => G i k ω * F i ω (ω (i, t0))) := by
        congr 1; funext ω; exact hsplit ω
      rw [h2]
      calc _ ≤ q * expect P (G i k) := key
        _ ≤ q * q ^ k := mul_le_mul_of_nonneg_left (ih (by omega)) hq0
        _ = q ^ (k + 1) := by ring
  -- feasibility
  have halloc : ∀ ω, IsAllocation (alloc ω) := by
    intro ω i j hij
    rw [Finset.disjoint_left]
    intro g hgi hgj
    simp only [alloc, Finset.mem_filter, Finset.mem_univ, true_and] at hgi hgj
    have h1 := hgi j (Ne.symm hij)
    have h2 := hgj i hij
    linarith
  -- failure bound
  have hfail : ∀ i, P.prob (fun ω => v i (alloc ω i) < 1 / 2) ≤ q ^ ℓ := by
    intro i
    rw [prob_eq_expect]
    refine le_trans (expect_mono P (H := G i ℓ) ?_) (hG i ℓ le_rfl)
    intro ω hω
    by_cases hf : v i (alloc ω i) < 1 / 2
    · rw [if_pos hf]
      have : G i ℓ ω = 1 := by
        simp only [G]
        apply Finset.prod_eq_one
        intro t _
        have hgd := hgood ω hω i
        simp only [F, hgd, true_and]
        rw [if_pos]
        intro hS
        apply absurd hf
        push Not
        refine le_trans hS (hmono i _ _ ?_)
        intro g hg
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
        simp only [alloc, Finset.mem_filter, Finset.mem_univ, true_and]
        intro j hj
        have h1 : tot ω j g ≤ cvec ω i g :=
          Finset.single_le_sum (f := fun j => tot ω j g) (fun j _ => htot0 ω hω j g)
            (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩)
        have h2 : (ω (i, t)).2 g ≤ tot ω i g :=
          Finset.single_le_sum (f := fun t => (ω (i, t)).2 g)
            (fun t _ => (hsupp ω hω i t).1 g) (Finset.mem_univ t)
        linarith
      rw [this]
    · rw [if_neg hf]
      exact Finset.prod_nonneg (fun t _ => hF0 _ _ _)
  refine ⟨map P alloc, ?_, ?_⟩
  · intro A hA
    obtain ⟨ω, _, rfl⟩ := Finset.mem_image.1 hA
    exact halloc ω
  · intro i
    rw [prob_map]
    exact hfail i

end SubadditiveMMS580.Amplification.Dev.T14
end

section
set_option autoImplicit false

open MultiAllocToAlloc.Subadditive

namespace SubadditiveMMS580.Amplification
open SubadditiveMMS580.Amplification.Dev.T14 SubadditiveMMS580.Amplification.Dev.FD in
theorem chk_theorem_1_4 (u n : ℕ) (hu : 2 ≤ u) (hn : 1 ≤ n) {m : ℕ}
    (v : Fin u → Finset (Fin m) → ℝ)
    (hnorm : ∀ i, IsNormalized (v i)) (hmono : ∀ i, IsMonotone (v i))
    (hsub : ∀ i, SubmodOrder.Subadditive (v i))
    (W : Fin u → Fin n → Finset (Fin m)) (hW : ∀ i, IsValuableFamily (v i) (W i))
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓn : 2 * ℓ * (u - 1) ≤ n) :
    (∃ σ : FinDist (Fin u → Finset (Fin m)),
      (∀ A ∈ σ.support, IsAllocation A) ∧
      ∀ i : Fin u, σ.prob (fun A => v i (A i) < 1 / 2) ≤
        ((1 : ℝ) / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / (n : ℝ)) ^ ℓ) ∧
    (4 * ℓ * (u - 1) ≤ n →
      ∃ A : Fin u → Finset (Fin m), IsAllocation A ∧
        (Finset.univ.filter (fun i => v i (A i) < 1 / 2)).card ≤
          ⌊(u : ℝ) * ((3 : ℝ) / 4) ^ ℓ⌋₊) := by
  classical
  obtain ⟨σ, hσA, hσp⟩ := part1_core u n hu hn v hnorm hmono hsub W hW ℓ hℓ
  refine ⟨⟨σ, hσA, hσp⟩, fun h4 => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast (by omega : 1 ≤ u)
  have h4R : (4 : ℝ) * ℓ * ((u : ℝ) - 1) ≤ n := by
    have : ((4 * ℓ * (u - 1) : ℕ) : ℝ) ≤ n := by exact_mod_cast h4
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ u)] at this
    simpa using this
  have hqle : (1 : ℝ) / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / n ≤ 3 / 4 := by
    have : (ℓ : ℝ) * ((u : ℝ) - 1) / n ≤ 1 / 4 := by
      rw [div_le_iff₀ hnR]; linarith
    linarith
  have hq0 : (0 : ℝ) ≤ (1 : ℝ) / 2 + (ℓ : ℝ) * ((u : ℝ) - 1) / n := by
    have : 0 ≤ (ℓ : ℝ) * ((u : ℝ) - 1) / n :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) hnR.le
    linarith
  have hpi : ∀ i, σ.prob (fun A => v i (A i) < 1 / 2) ≤ ((3 : ℝ) / 4) ^ ℓ := fun i =>
    le_trans (hσp i) (pow_le_pow_left₀ hq0 hqle ℓ)
  set M : ℝ := (u : ℝ) * ((3 : ℝ) / 4) ^ ℓ with hM
  have hcount : ∀ A : Fin u → Finset (Fin m),
      ((Finset.univ.filter (fun i => v i (A i) < 1 / 2)).card : ℝ) =
        ∑ i, (if v i (A i) < 1 / 2 then (1 : ℝ) else 0) := by
    intro A
    rw [Finset.card_filter]; push_cast; rfl
  have hE : expect σ (fun A => ((Finset.univ.filter (fun i => v i (A i) < 1 / 2)).card : ℝ)) ≤ M := by
    simp_rw [hcount]
    rw [expect_sum]
    calc ∑ i, expect σ (fun A => if v i (A i) < 1 / 2 then (1 : ℝ) else 0)
        = ∑ i, σ.prob (fun A => v i (A i) < 1 / 2) :=
          Finset.sum_congr rfl (fun i _ => (prob_eq_expect σ _).symm)
      _ ≤ ∑ _i : Fin u, ((3 : ℝ) / 4) ^ ℓ := Finset.sum_le_sum (fun i _ => hpi i)
      _ = M := by simp [hM]
  by_contra hcon
  push Not at hcon
  have hall : ∀ A ∈ σ.support, ⌊M⌋₊ + 1 ≤ (Finset.univ.filter (fun i => v i (A i) < 1 / 2)).card := by
    intro A hA
    have := hcon A (hσA A hA)
    omega
  have h1 : expect σ (fun _ => ((⌊M⌋₊ : ℝ) + 1)) ≤
      expect σ (fun A => ((Finset.univ.filter (fun i => v i (A i) < 1 / 2)).card : ℝ)) :=
    expect_mono σ (fun A hA => by exact_mod_cast hall A hA)
  rw [expect_const] at h1
  have := Nat.lt_floor_add_one M
  linarith

end SubadditiveMMS580.Amplification
end

theorem solution : type_of% @SubadditiveMMS580.Amplification.chk_theorem_1_4 := @SubadditiveMMS580.Amplification.chk_theorem_1_4
