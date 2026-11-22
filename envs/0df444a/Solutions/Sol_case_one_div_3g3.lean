-- Prove2me | solution 1 for case_one_div_3g3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:23.817321+00:00
-- url     : https://prove2.me/submissions/cbecbab8-2496-4068-a198-da673191dd62

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
import Theorems.Thm_polychromNumber_pair
import Theorems.Thm_polychromNumber_singleton
import Theorems.Thm_polychromNumber_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ
attribute [local simp] polychromNumber_pair
attribute [local simp] polychromNumber_singleton
attribute [local simp] polychromNumber_univ


section
open Finset Pointwise
section Case1_SingleCycle
variable (m : ℕ)
private lemma endgame_witness {g : ℕ} {c : ℕ → ℕ} {v s : ℕ} {k : Fin 3} (hs : s < 3) (a₀ a₁ a₂ : ℕ)
    (ha₀ : a₀ ∈ ({0, 1, g, g + 1} : Finset ℕ))
    (ha₁ : a₁ ∈ ({0, 1, g, g + 1} : Finset ℕ))
    (ha₂ : a₂ ∈ ({0, 1, g, g + 1} : Finset ℕ))
    (hc₀ : c (v + a₀) = s)
    (hc₁ : c (v + a₁) = (s + 1) % 3)
    (hc₂ : c (v + a₂) = (s + 2) % 3) :
    ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (v + a) = k.val := by grind
private lemma lift_coloring_witness {m g : ℕ} [NeZero m] [Fact (1 < m)]
    (hg_lt : g + 1 < m) {c : ℕ → ℕ} (hc_lt : ∀ p, c p < 3)
    (hc_period : ∀ p, c (p % m) = c p)
    {n : ZMod m} {k : Fin 3}
    (h : ∃ a ∈ ({0, 1, g, g + 1} : Finset ℕ), c (n.val + a) = k.val) :
    ∃ s ∈ ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)),
      (⟨c (n + s).val, hc_lt _⟩ : Fin 3) = k := by
  obtain ⟨a, ha, hca⟩ := h
  have ha_lt : a < m := by grind
  exact ⟨(a : ZMod m),
    by simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
       rcases ha with rfl | rfl | rfl | rfl <;> simp,
    by ext
       change c (n + (a : ZMod m)).val = k.val
       have : (n + (a : ZMod m)).val = (n.val + a) % m := by
         rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt ha_lt]
       rw [this, hc_period, hca]⟩
section Case1c
end Case1c
section Case1d
end Case1d
end Case1_SingleCycle
end

set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (g : ℕ) (hm_eq : m = 3 * g + 3) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  haveI : NeZero m := ⟨by grind⟩
  haveI : Fact (1 < m) := ⟨by grind⟩
  obtain ⟨t, ht⟩ := hg3
  set h := g + 1
  have hh_pos : 0 < h := by grind
  let c (p : ℕ) : ℕ := (p % h % 3 + (3 - p / h % 3)) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by grind)
  have hc_period : ∀ p, c (p % m) = c p := by
    have hm3h : m = 3 * h := by grind
    intro p
    simp only [c, hm3h]
    have hp_eq : p = h * (3 * (p / (3 * h))) + p % (3 * h) := by grind [Nat.mod_add_div p (3 * h)]
    conv_rhs => rw [hp_eq]
    grind [Nat.mul_add_mod, Nat.add_mul_div_left]
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness (by grind) hc_lt3 hc_period ?_⟩
  set v := n.val
  set r := v % h
  set q := v / h
  have hv_eq : v = h * q + r := (Nat.div_add_mod v h).symm
  have hr_lt : r < h := Nat.mod_lt _ hh_pos
  have color_at : ∀ q' r', r' < h →
      c (h * q' + r') = (r' % 3 + (3 - q' % 3)) % 3 := fun q' r' hr' => by
    change ((h * q' + r') % h % 3 + (3 - (h * q' + r') / h % 3)) % 3 = _
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr',
        Nat.mul_add_div hh_pos, Nat.div_eq_of_lt hr', add_zero]
  by_cases hrg : r = g
  · have hcv : c v = (3 - q % 3) % 3 := by grind
    have hcvg : c (v + g) = (2 + (3 - (q + 1) % 3)) % 3 := by
      have : v + g = h * (q + 1) + (g - 1) := by grind
      rw [this, color_at (q + 1) (g - 1) (by grind)]
      grind
    have hcv1 : c (v + 1) = (3 - (q + 1) % 3) % 3 := by
      have : v + 1 = h * (q + 1) + 0 := by grind
      rw [this, color_at (q + 1) 0 (by grind)]
      grind
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by grind) (by grind)
  · have hcv1 : c (v + 1) = ((r + 1) % 3 + (3 - q % 3)) % 3 := by
      have : v + 1 = h * q + (r + 1) := by grind
      rw [this, color_at q (r + 1) (by grind)]
    have hcvg1 : c (v + g + 1) = (r % 3 + (3 - (q + 1) % 3)) % 3 := by
      have : v + g + 1 = h * (q + 1) + r := by grind
      rw [this, color_at (q + 1) r hr_lt]
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 1 (g + 1)
      (by simp) (by simp) (by simp) rfl
      (by grind)
      (by grind)
