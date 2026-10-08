-- Prove2me | solution 1 for PermLimits.Cauchy.eventually_const_of_convergent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T00:18:59.190326+00:00
-- url     : https://prove2.me/submissions/7d2ac8c3-0399-4d37-b67b-de6d15b33fba

import Mathlib
import Definitions.Def_PermLimits_Shared_PermDensity

set_option autoImplicit false

open PermLimits.Shared Filter

namespace PermLimitsEC18

lemma pattern_exists {j m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Fin j → Fin m)
    (hx : ∀ i i', i < i' → x i < x i') :
    ∃ τ : Equiv.Perm (Fin j), ∀ i i', (σ (x i) < σ (x i') ↔ τ i < τ i') := by
  classical
  have hxi : Function.Injective x := (StrictMono.injective (fun a b h => hx a b h))
  set g : Fin j → Fin m := fun i => σ (x i) with hg
  have ginj : Function.Injective g := σ.injective.comp hxi
  set S : Finset (Fin m) := Finset.univ.image g with hS
  have hcard : S.card = j := by
    rw [hS, Finset.card_image_of_injective _ ginj]; simp
  let e : Fin j ≃o S := S.orderIsoOfFin hcard
  have hmem : ∀ i, g i ∈ S := fun i => Finset.mem_image_of_mem g (Finset.mem_univ i)
  let τ₀ : Fin j → Fin j := fun i => e.symm ⟨g i, hmem i⟩
  have key : ∀ i i', (g i < g i' ↔ τ₀ i < τ₀ i') := by
    intro i i'
    simp only [τ₀, e.symm.lt_iff_lt]
    rfl
  have τinj : Function.Injective τ₀ := by
    intro a b h
    have : (⟨g a, hmem a⟩ : S) = ⟨g b, hmem b⟩ := e.symm.injective h
    exact ginj (congrArg Subtype.val this)
  refine ⟨Equiv.ofBijective τ₀ (Finite.injective_iff_bijective.mp τinj), ?_⟩
  intro i i'
  exact key i i'

lemma choose_le_incr (j m : ℕ) :
    Nat.choose m j ≤ (Finset.univ.filter
      (fun x : Fin j → Fin m => ∀ i i', i < i' → x i < x i')).card := by
  classical
  have h1 : (Finset.powersetCard j (Finset.univ : Finset (Fin m))).card = Nat.choose m j := by
    rw [Finset.card_powersetCard]; simp
  rw [← h1]
  apply Finset.card_le_card_of_surjOn (fun x : Fin j → Fin m => Finset.univ.image x)
  intro t ht
  rw [Finset.mem_coe, Finset.mem_powersetCard] at ht
  refine ⟨t.orderEmbOfFin ht.2, ?_, ?_⟩
  · rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i i' h => (t.orderEmbOfFin ht.2).strictMono h⟩
  · exact Finset.image_orderEmbOfFin_univ t ht.2

lemma incr_le_sum_occ {j m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (Finset.univ.filter
      (fun x : Fin j → Fin m => ∀ i i', i < i' → x i < x i')).card ≤
      ∑ τ : Equiv.Perm (Fin j), occurrences τ σ := by
  classical
  unfold occurrences
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro x hx
  rw [Finset.mem_filter] at hx
  obtain ⟨τ, hτ⟩ := pattern_exists σ x hx.2
  rw [Finset.mem_biUnion]
  refine ⟨τ, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hx.2, hτ⟩

lemma one_le_sum_density {j m : ℕ} (hjm : j ≤ m) (σ : Equiv.Perm (Fin m)) :
    1 ≤ ∑ τ : Equiv.Perm (Fin j), permDensity τ σ := by
  have hc : (0 : ℝ) < (Nat.choose m j : ℝ) := by exact_mod_cast Nat.choose_pos hjm
  have hle : (Nat.choose m j : ℝ) ≤ ∑ τ : Equiv.Perm (Fin j), (occurrences τ σ : ℝ) := by
    exact_mod_cast le_trans (choose_le_incr j m) (incr_le_sum_occ σ)
  have : ∑ τ : Equiv.Perm (Fin j), permDensity τ σ
      = (∑ τ : Equiv.Perm (Fin j), (occurrences τ σ : ℝ)) / (Nat.choose m j : ℝ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro τ _
    simp [permDensity, hjm]
  rw [this, le_div_iff₀ hc, one_mul]
  exact hle

lemma perm_eq_of_order {k : ℕ} (σ π : Equiv.Perm (Fin k))
    (h : ∀ i j, (σ i < σ j ↔ π i < π j)) : σ = π := by
  have hmono : StrictMono (fun a => σ (π.symm a)) := by
    intro a b hab
    rw [h]; simpa using hab
  have hid := hmono.eq_id
  ext i
  have := congrFun hid (π i)
  simp at this
  rw [this]

lemma density_self_pos {k : ℕ} (π : Equiv.Perm (Fin k)) : 1 ≤ permDensity π π := by
  classical
  have hocc : 1 ≤ occurrences π π := by
    unfold occurrences
    apply Finset.one_le_card.mpr
    refine ⟨id, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i j h => h, fun i j => Iff.rfl⟩
  simp only [permDensity, le_refl, if_true, Nat.choose_self, Nat.cast_one, div_one]
  exact_mod_cast hocc

lemma eq_of_density_pos {k m : ℕ} (π : Equiv.Perm (Fin k)) (σ : Equiv.Perm (Fin m))
    (hm : m ≤ k) (hpos : 0 < permDensity π σ) : (⟨m, σ⟩ : Σ n : ℕ, Equiv.Perm (Fin n)) = ⟨k, π⟩ := by
  classical
  unfold permDensity at hpos
  split_ifs at hpos with hkm
  swap
  · exact absurd hpos (lt_irrefl _)
  have hmk : m = k := le_antisymm hm hkm
  subst hmk
  have hocc : 0 < occurrences π σ := by
    by_contra hc
    push Not at hc
    have : occurrences π σ = 0 := Nat.le_zero.mp hc
    rw [this] at hpos; simp at hpos
  unfold occurrences at hocc
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hocc
  rw [Finset.mem_filter] at hx
  have hxid : x = id := StrictMono.eq_id (fun a b h => hx.2.1 a b h)
  subst hxid
  have := perm_eq_of_order σ π (fun i j => hx.2.2 i j)
  rw [this]

end PermLimitsEC18

open PermLimits.Shared Filter in
theorem solution (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n))
    (hconv : IsConvergent s) (hs : ¬ Tendsto (fun n => (s n).1) atTop atTop) :
    ∃ (p : Σ n : ℕ, Equiv.Perm (Fin n)) (n₀ : ℕ), ∀ n, n₀ ≤ n → s n = p := by
  -- bound B with lengths frequently below B
  rw [tendsto_atTop] at hs
  push Not at hs
  obtain ⟨B, hB⟩ := hs
  have hBf : ∃ᶠ n in atTop, (s n).1 < B := by
    simpa [Filter.Frequently, not_le] using hB
  -- pigeonhole
  set S : Set (Σ n : ℕ, Equiv.Perm (Fin n)) := {p | p.1 < B} with hSdef
  have hSfin : S.Finite := by
    refine (Set.finite_range (fun q : (Σ i : Fin B, Equiv.Perm (Fin i)) =>
      (⟨q.1.val, q.2⟩ : Σ n : ℕ, Equiv.Perm (Fin n)))).subset ?_
    rintro ⟨n, π⟩ hp
    exact ⟨⟨⟨n, hp⟩, π⟩, rfl⟩
  have hfreq : ∃ p ∈ S, ∃ᶠ n in atTop, s n = p := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ p ∈ S, ∀ᶠ n in atTop, s n ≠ p := by
      intro p hp
      have := hcon p hp
      simpa [Filter.Frequently] using this
    have hev := (Filter.eventually_all_finite hSfin).2 hall
    have := hBf.and_eventually hev
    obtain ⟨n, h1, h2⟩ := this.exists
    exact h2 (s n) h1 rfl
  obtain ⟨⟨k, π⟩, -, hp⟩ := hfreq
  -- eventually length ≤ k
  have hlim0 : ∀ τ : Equiv.Perm (Fin (k + 1)),
      Tendsto (fun n => permDensity τ (s n).2) atTop (nhds 0) := by
    intro τ
    obtain ⟨L, hL⟩ := hconv (k + 1) τ
    have hL0 : L = 0 := by
      have hfr : ∃ᶠ n in atTop, permDensity τ (s n).2 ∈ ({0} : Set ℝ) := by
        refine hp.mono ?_
        intro n hn
        rw [hn]
        simp [permDensity]
      exact isClosed_singleton.mem_of_frequently_of_tendsto hfr hL
    rw [hL0] at hL
    exact hL
  have hsum : Tendsto (fun n => ∑ τ : Equiv.Perm (Fin (k + 1)), permDensity τ (s n).2)
      atTop (nhds 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin (k + 1))))
      (fun τ _ => hlim0 τ)
    simpa using this
  have hevlen : ∀ᶠ n in atTop, (s n).1 ≤ k := by
    filter_upwards [(tendsto_order.1 hsum).2 1 one_pos] with n hn
    by_contra hc
    push Not at hc
    have := PermLimitsEC18.one_le_sum_density (j := k + 1) hc (s n).2
    linarith
  -- eventually density of π positive
  obtain ⟨L, hL⟩ := hconv k π
  have hL1 : L ∈ Set.Ici (1 : ℝ) := by
    have hfr : ∃ᶠ n in atTop, permDensity π (s n).2 ∈ Set.Ici (1 : ℝ) := by
      refine hp.mono ?_
      intro n hn
      rw [hn]
      exact PermLimitsEC18.density_self_pos π
    exact isClosed_Ici.mem_of_frequently_of_tendsto hfr hL
  have hevpos : ∀ᶠ n in atTop, 0 < permDensity π (s n).2 :=
    (tendsto_order.1 hL).1 0 (by simp at hL1; linarith)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hevlen.and hevpos)
  refine ⟨⟨k, π⟩, n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn₀ n hn
  have := PermLimitsEC18.eq_of_density_pos π (s n).2 h1 h2
  exact this
