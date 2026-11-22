-- Prove2me | solution 1 for case_one_div_3g
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:49:16.154257+00:00
-- url     : https://prove2.me/submissions/d0ee32d4-c00d-40c6-9a81-8a63f378fb46

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
theorem _root_.solution (g : ℕ) (hm_eq : m = 3 * g) (hg3 : 3 ∣ g) (hg : 0 < g) :
    HasPolychromColouring (Fin 3) ({0, 1, (g : ZMod m), (g : ZMod m) + 1} : Finset (ZMod m)) := by
  haveI : NeZero m := ⟨by grind⟩
  haveI : Fact (1 < m) := ⟨by grind⟩
  obtain ⟨t, ht⟩ := hg3
  let c (p : ℕ) : ℕ := (p % 3 + p / g) % 3
  have hc_lt3 : ∀ p, c p < 3 := fun p => Nat.mod_lt _ (by grind)
  have hc_period : ∀ p, c (p % m) = c p := by
    intro p
    simp only [c, hm_eq]
    rw [Nat.mod_mod_of_dvd p (dvd_mul_right 3 g)]
    have h2 : p = p % (3 * g) + 3 * (p / (3 * g)) * g := by grind [Nat.mod_add_div p (3 * g)]
    have h3 : p / g = p % (3 * g) / g + 3 * (p / (3 * g)) := by
      conv_lhs => rw [h2]; exact Nat.add_mul_div_right _ _ hg
    grind
  refine ⟨fun x => ⟨c x.val, hc_lt3 _⟩, fun n k =>
    lift_coloring_witness (by grind) hc_lt3 hc_period ?_⟩
  set v := n.val
  set r := v % g
  set q := v / g
  have hv_eq : v = g * q + r := (Nat.div_add_mod v g).symm
  have hr_lt : r < g := Nat.mod_lt _ hg
  have gk_mod3 : ∀ k a, (g * k + a) % 3 = a % 3 := fun k a => by
    rw [ht]; grind [Nat.mul_add_mod]
  have color_at : ∀ q' r', r' < g → c (g * q' + r') = (r' % 3 + q') % 3 := fun q' r' hr' => by
    simp only [c, gk_mod3, Nat.mul_add_div hg, Nat.div_eq_of_lt hr', add_zero]
  by_cases hr_lt_gm1 : r + 1 < g
  · have hcv : c v = (r % 3 + q) % 3 := hv_eq ▸ color_at q r hr_lt
    have hcvg : c (v + g) = (r % 3 + (q + 1)) % 3 := by grind [color_at (q + 1) r hr_lt]
    have hcvg1 : c (v + g + 1) = ((r + 1) % 3 + (q + 1)) % 3 := by
      grind [color_at (q + 1) (r + 1) (by grind)]
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g (g + 1)
      (by simp) (by simp) (by simp)
      hcv (by grind) (by grind)
  · push Not at hr_lt_gm1
    have hr_eq : r = g - 1 := by grind
    have hcv : c v = (2 + q) % 3 := by grind
    have hcv1 : c (v + 1) = (q + 1) % 3 := by grind [color_at (q + 1) 0 hg]
    have hcvg : c (v + g) = (2 + (q + 1)) % 3 := by
      have : v + g = g * (q + 1) + (g - 1) := by grind
      grind
    exact endgame_witness (Nat.mod_lt _ (by grind)) 0 g 1
      (by simp) (by simp) (by simp)
      hcv (by grind) (by grind)
