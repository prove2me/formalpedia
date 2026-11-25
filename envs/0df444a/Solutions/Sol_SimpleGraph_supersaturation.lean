-- Prove2me | solution 1 for SimpleGraph.supersaturation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:56:47.806345+00:00
-- url     : https://prove2.me/submissions/8887e8f8-e91d-4336-93da-d2832fbbf739

module
public import Definitions.Def_GoodmanSupersaturation_Goodman
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_GoodmanSupersaturation_Supersaturation
public import Theorems.Thm_SimpleGraph_cliqueCountIn_mono
public import Theorems.Thm_SimpleGraph_cliqueCountIn_one
public import Theorems.Thm_SimpleGraph_sum_cliqueCountIn_neighbors_le
public import Theorems.Thm_SimpleGraph_cliqueCountIn_univ
public import Theorems.Thm_SimpleGraph_degreeWithin_univ
attribute [local simp] SimpleGraph.cliqueCountIn_univ
attribute [local simp] SimpleGraph.degreeWithin_univ


attribute [local simp] SimpleGraph.cliqueCountIn_one
section
@[expose] public section
open Finset
namespace SimpleGraph
variable {V : Type*}
section Recursion
variable [DecidableEq V]
private theorem bound_mono (k l : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    supersaturationBound k l x ≤ supersaturationBound k l y := by
  unfold supersaturationBound
  gcongr
private theorem bound_nonneg (k l : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ supersaturationBound k l x := by
  unfold supersaturationBound
  positivity
private theorem bound_succ (k l : ℕ) (x : ℝ) :
    supersaturationBound k (l + 1) x = supersaturationBound k l (x / 2) := by
  unfold supersaturationBound
  rw [show k * (l + 1) = k * l + k by ring, div_pow, pow_add, pow_add]
  field_simp
  ring
private theorem bound_one_le (j : ℕ) (hj : 2 ≤ j) {x : ℝ} (hx : 0 ≤ x) :
    supersaturationBound 1 j x ≤ x := by
  unfold supersaturationBound
  rw [show ((1 : ℕ) + 1).choose 2 = 1 from rfl, Nat.factorial_one, Nat.cast_one, one_mul, pow_one,
    show 2 * 1 + 1 = 3 from rfl, one_mul]
  rw [div_le_iff₀ (by positivity)]
  have : (2 : ℝ) ^ 3 ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith
private theorem bound_step (a c : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    supersaturationBound (a + 1) (c + 2) x ≤
      x / (2 * ((a : ℝ) + 1)) * supersaturationBound a (c + 2) (x / 2) := by
  have hf : (((a + 1).factorial : ℕ) : ℝ) = ((a : ℝ) + 1) * (a.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hch : (a + 1 + 1).choose 2 = (a + 1).choose 2 + (a + 1) := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  have key : x / (2 * ((a : ℝ) + 1)) * supersaturationBound a (c + 2) (x / 2) =
      supersaturationBound (a + 1) (c + 2) x * 2 ^ c := by
    unfold supersaturationBound
    rw [hf, hch, show (a + 1) * (c + 2) = a * (c + 2) + (c + 2) by ring, div_pow,
      pow_add, pow_add, pow_add, pow_succ, pow_succ]
    field_simp
    ring
  rw [key]
  have : (1 : ℝ) ≤ 2 ^ c := one_le_pow₀ (by norm_num)
  have := bound_nonneg (a + 1) (c + 2) hx
  nlinarith
variable (G : SimpleGraph V) [DecidableRel G.Adj]
private theorem card_nbhd_add (S : Finset V) {v : V} (hv : v ∈ S) :
    #(nbhd G S v) + #(nbhd Gᶜ S v) + 1 = #S := by
  have h1 : nbhd G S v = {w ∈ S.erase v | G.Adj v w} := by
    ext w
    simp only [mem_filter, mem_erase]
    exact ⟨fun ⟨hw, ha⟩ => ⟨⟨(G.ne_of_adj ha).symm, hw⟩, ha⟩, fun ⟨⟨_, hw⟩, ha⟩ => ⟨hw, ha⟩⟩
  have h2 : nbhd Gᶜ S v = {w ∈ S.erase v | ¬G.Adj v w} := by
    ext w
    simp only [mem_filter, mem_erase, compl_adj]
    exact ⟨fun ⟨hw, hne, hna⟩ => ⟨⟨Ne.symm hne, hw⟩, hna⟩,
      fun ⟨⟨hne, hw⟩, hna⟩ => ⟨hw, Ne.symm hne, hna⟩⟩
  rw [h1, h2, card_filter_add_card_filter_not, card_erase_of_mem hv]
  have : 0 < #S := card_pos.mpr ⟨v, hv⟩
  omega
private theorem exists_half (S : Finset V) :
    (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)} : ℝ) ∨
      (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd G S v)} : ℝ) := by
  set A := {v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)}
  set B := {v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd G S v)}
  have hsub : S ⊆ A ∪ B := fun v hv => by
    have hd : (#(nbhd G S v) : ℝ) + #(nbhd Gᶜ S v) + 1 = #S := by
      exact_mod_cast card_nbhd_add G S hv
    rw [mem_union]
    by_cases hb : ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)
    · exact .inl (mem_filter.mpr ⟨hv, hb⟩)
    · exact .inr (mem_filter.mpr ⟨hv, by linarith⟩)
  have : (#S : ℝ) ≤ #A + #B := by exact_mod_cast (card_le_card hsub).trans (card_union_le A B)
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  linarith [hcon.1, hcon.2]
omit G in
private theorem claim_symm {k l : ℕ} (h : Claim V k l) : Claim V l k := by
  intro G _ S hx
  have hx' : 0 < (#S : ℝ) + 1 - 2 ^ (k + l - 3) := by rwa [Nat.add_comm] at hx
  rw [show l + k - 3 = k + l - 3 by omega]
  rcases h Gᶜ S hx' with h1 | h1
  · exact .inr h1
  · left
    convert h1 using 2
    simp only [cliqueCountIn, compl_compl]
omit G in
private theorem claim_one_left {l : ℕ} (hl : 2 ≤ l) : Claim V 1 l := by
  intro G _ S hx
  left
  rw [cliqueCountIn_one]
  have h1 : (1 : ℝ) ≤ 2 ^ (1 + l - 3) := one_le_pow₀ (by norm_num)
  have := bound_one_le l hl hx.le
  linarith
omit G in
private theorem claim_one_right {k : ℕ} (hk : 2 ≤ k) : Claim V k 1 :=
  claim_symm (claim_one_left hk)
omit G in
private theorem step {c l : ℕ} (IH : Claim V (c + 2) l) (hl : 1 ≤ l)
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3))
    (hgood : (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)} : ℝ)) :
    supersaturationBound (c + 2) (l + 1) ((#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3)) ≤
        G.cliqueCountIn S (c + 2) ∨
      supersaturationBound (l + 1) (c + 2) ((#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3)) ≤
        Gᶜ.cliqueCountIn S (l + 1) := by
  set x : ℝ := (#S : ℝ) + 1 - 2 ^ (c + 2 + (l + 1) - 3) with hxdef
  set good := {v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜ S v)} with hgooddef
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hpow : (2 : ℝ) ^ (c + 2 + (l + 1) - 3) = 2 * 2 ^ (c + 2 + l - 3) := by
    rw [show c + 2 + (l + 1) - 3 = (c + 2 + l - 3) + 1 by omega, pow_succ]; ring
  have hx2 : 0 < x / 2 := by linarith
  have hv : ∀ v ∈ good,
      supersaturationBound l (c + 2) (x / 2) ≤ Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l := by
    intro v hvg
    have hdeg := (mem_filter.mp hvg).2
    set W := nbhd Gᶜ S v
    have hxW : x / 2 ≤ (#W : ℝ) + 1 - 2 ^ (c + 2 + l - 3) := by rw [hxdef, hpow]; linarith
    rcases IH G W (by linarith) with h | h
    · exfalso
      have : supersaturationBound (c + 2) (l + 1) x ≤ G.cliqueCountIn S (c + 2) := by
        calc supersaturationBound (c + 2) (l + 1) x
            = supersaturationBound (c + 2) l (x / 2) := bound_succ _ _ _
          _ ≤ supersaturationBound (c + 2) l ((#W : ℝ) + 1 - 2 ^ (c + 2 + l - 3)) :=
              bound_mono _ _ hx2.le hxW
          _ ≤ G.cliqueCountIn W (c + 2) := h
          _ ≤ G.cliqueCountIn S (c + 2) := by
              exact_mod_cast cliqueCountIn_mono G (filter_subset _ _) (c + 2)
      linarith
    · exact (bound_mono _ _ hx2.le hxW).trans h
  set B := supersaturationBound l (c + 2) (x / 2)
  have hB0 : 0 ≤ B := bound_nonneg _ _ hx2.le
  have hsum : (#good : ℝ) * B ≤ ∑ v ∈ good, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) := by
    simpa [nsmul_eq_mul] using card_nsmul_le_sum good _ B hv
  have hsub : ∑ v ∈ good, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) ≤
      ∑ v ∈ S, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
  have hdc : ∑ v ∈ S, (Gᶜ.cliqueCountIn (nbhd Gᶜ S v) l : ℝ) ≤
      ((l : ℝ) + 1) * Gᶜ.cliqueCountIn S (l + 1) := by
    have := sum_cliqueCountIn_neighbors_le Gᶜ S (j := l + 1) (by omega)
    simp only [Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hxm : x ≤ #S := by
    have : (1 : ℝ) ≤ 2 ^ (c + 2 + (l + 1) - 3) := one_le_pow₀ (by norm_num)
    rw [hxdef]; linarith
  have hstep := bound_step (a := l) (c := c) hx.le
  have hcc : x / 2 * B ≤ ((l : ℝ) + 1) * Gᶜ.cliqueCountIn S (l + 1) := by
    have e1 : x / 2 * B ≤ (#S : ℝ) / 2 * B := mul_le_mul_of_nonneg_right (by linarith) hB0
    have e2 : (#S : ℝ) / 2 * B ≤ (#good : ℝ) * B := mul_le_mul_of_nonneg_right hgood hB0
    linarith
  have hfin : supersaturationBound (l + 1) (c + 2) x ≤ Gᶜ.cliqueCountIn S (l + 1) := by
    refine hstep.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith
omit G in
private theorem claim_all :
    ∀ n k l : ℕ, 1 ≤ k → 1 ≤ l → 3 ≤ k + l → k + l = n → Claim V k l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k l hk hl h3 hn
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · obtain rfl : k = 1 := by omega
      exact claim_one_left (by omega)
    rcases Nat.lt_or_ge l 2 with hl1 | hl2
    · obtain rfl : l = 1 := by omega
      exact claim_one_right hk2
    obtain ⟨c, rfl⟩ : ∃ c, k = c + 2 := ⟨k - 2, by omega⟩
    obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    have IH1 : Claim V (c + 2) l' := ih _ (by omega) _ _ (by omega) (by omega) (by omega) rfl
    have IH2 : Claim V (c + 1) (l' + 1) := ih _ (by omega) _ _ (by omega) (by omega) (by omega) rfl
    intro G _ S hx
    rcases exists_half G S with hbl | hrd
    · exact step IH1 (by omega) G S hx hbl
    · obtain ⟨c', rfl⟩ : ∃ c', l' = c' + 1 := ⟨l' - 1, by omega⟩
      have e : c' + 2 + (c + 1 + 1) - 3 = c + 2 + (c' + 1 + 1) - 3 := by omega
      have hrd' : (#S : ℝ) / 2 ≤ (#{v ∈ S | ((#S : ℝ) - 1) / 2 ≤ #(nbhd Gᶜᶜ S v)} : ℝ) := by
        simpa only [compl_compl] using hrd
      have := step (G := Gᶜ) (claim_symm IH2) (by omega) S (by rw [e]; exact hx) hrd'
      rw [e] at this
      rcases this with h | h
      · exact .inr h
      · left
        convert h using 2
        simp only [cliqueCountIn, compl_compl]
end Recursion
end SimpleGraph
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*}
variable [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (h3 : 3 ≤ k + l) (S : Finset V)
    (hx : 0 < (#S : ℝ) + 1 - 2 ^ (k + l - 3)) :
    supersaturationBound k l ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ G.cliqueCountIn S k ∨
      supersaturationBound l k ((#S : ℝ) + 1 - 2 ^ (k + l - 3)) ≤ Gᶜ.cliqueCountIn S l :=
  claim_all (k + l) k l hk hl h3 rfl G S hx
end SimpleGraph
