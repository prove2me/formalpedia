-- Prove2me | solution 1 for PathsTreesFlowers.Invariance.lemma_4_14_expansion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T10:30:47.843608+00:00
-- url     : https://prove2.me/submissions/a9046d14-5a6d-408c-800c-b43147f51feb

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Sym2
import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_PathsTreesFlowers_Invariance_Basic
import Definitions.Def_PathsTreesFlowers_Invariance_Shrink

namespace SolPathsTreesFlowersLemma414Expansion

set_option linter.unusedSectionVars false

open EdmondsMatching65.Polyhedron (IsMatching)
open PathsTreesFlowers.Invariance

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Part 1: Modular shift on `Fin (2 * k + 1)` -/

def shiftFin (k : ℕ) (hk : 1 ≤ k) (i₀ : Fin (2 * k + 1)) (m : ℕ) : Fin (2 * k + 1) :=
  ⟨(i₀.1 + m) % (2 * k + 1), Nat.mod_lt _ (by omega)⟩

lemma shiftFin_zero (k : ℕ) (hk : 1 ≤ k) (i₀ : Fin (2 * k + 1)) :
    shiftFin k hk i₀ 0 = i₀ := by
  ext
  simp [shiftFin, Nat.mod_eq_of_lt i₀.2]

lemma shiftFin_add_one (k : ℕ) (hk : 1 ≤ k) (i₀ : Fin (2 * k + 1)) (m : ℕ) :
    shiftFin k hk i₀ m + 1 = shiftFin k hk i₀ (m + 1) := by
  ext
  rw [Fin.val_add]
  have h1 : (1 : Fin (2 * k + 1)).1 = 1 := by
    change 1 % (2 * k + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1]
  dsimp [shiftFin]
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma shiftFin_inj_of_lt (k : ℕ) (hk : 1 ≤ k) (i₀ : Fin (2 * k + 1))
    {m₁ m₂ : ℕ} (hm₁ : m₁ < 2 * k + 1) (hm₂ : m₂ < 2 * k + 1)
    (heq : shiftFin k hk i₀ m₁ = shiftFin k hk i₀ m₂) : m₁ = m₂ := by
  have hval : (i₀.1 + m₁) % (2 * k + 1) = (i₀.1 + m₂) % (2 * k + 1) :=
    congrArg Fin.val heq
  have hi₀ := i₀.2
  by_cases h1 : i₀.1 + m₁ < 2 * k + 1 <;> by_cases h2 : i₀.1 + m₂ < 2 * k + 1
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval
    omega
  · have h2' : (i₀.1 + m₂) % (2 * k + 1) = i₀.1 + m₂ - (2 * k + 1) := by
      conv_lhs => rw [show i₀.1 + m₂ = (i₀.1 + m₂ - (2 * k + 1)) + (2 * k + 1) by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [Nat.mod_eq_of_lt h1, h2'] at hval
    omega
  · have h1' : (i₀.1 + m₁) % (2 * k + 1) = i₀.1 + m₁ - (2 * k + 1) := by
      conv_lhs => rw [show i₀.1 + m₁ = (i₀.1 + m₁ - (2 * k + 1)) + (2 * k + 1) by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1', Nat.mod_eq_of_lt h2] at hval
    omega
  · have h1' : (i₀.1 + m₁) % (2 * k + 1) = i₀.1 + m₁ - (2 * k + 1) := by
      conv_lhs => rw [show i₀.1 + m₁ = (i₀.1 + m₁ - (2 * k + 1)) + (2 * k + 1) by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have h2' : (i₀.1 + m₂) % (2 * k + 1) = i₀.1 + m₂ - (2 * k + 1) := by
      conv_lhs => rw [show i₀.1 + m₂ = (i₀.1 + m₂ - (2 * k + 1)) + (2 * k + 1) by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1', h2'] at hval
    omega

lemma shiftFin_surj (k : ℕ) (hk : 1 ≤ k) (i₀ i : Fin (2 * k + 1)) :
    ∃ m < 2 * k + 1, shiftFin k hk i₀ m = i := by
  have hi₀ := i₀.2
  have hi := i.2
  by_cases hle : i₀.1 ≤ i.1
  · refine ⟨i.1 - i₀.1, by omega, ?_⟩
    ext
    dsimp [shiftFin]
    rw [show i₀.1 + (i.1 - i₀.1) = i.1 by omega, Nat.mod_eq_of_lt hi]
  · refine ⟨i.1 + (2 * k + 1) - i₀.1, by omega, ?_⟩
    ext
    dsimp [shiftFin]
    rw [show i₀.1 + (i.1 + (2 * k + 1) - i₀.1) = i.1 + (2 * k + 1) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-! ### Part 2: Internal matching of an `IsOddCircuitSet` with any prescribed exposed vertex -/

lemma oddCircuitSet_matching_any_exposed {G : EdmondsMatching65.Polyhedron.Graph V E}
    {U : Finset V} (hodd : IsOddCircuitSet G U) :
    ∀ u ∈ U, ∃ MP : Finset E, MP ⊆ (induced G U).edges ∧ IsMatching G MP ∧
      (∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) := by
  induction hodd with
  | singleton v =>
    intro u hu
    have huv : u = v := Finset.mem_singleton.mp hu
    subst huv
    refine ⟨∅, Finset.empty_subset _, fun _ he => False.elim (Finset.notMem_empty _ he), ?_⟩
    intro w hw
    rw [Finset.mem_singleton.mp hw]
    exact ⟨fun _ => rfl, fun _ _ he => False.elim (Finset.notMem_empty _ he)⟩
  | circuit k hk Uf ef _hUf hdisj hends ih =>
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨i₀, _, hui₀⟩
    let sh := shiftFin k hk i₀
    have hsh0 : sh 0 = i₀ := shiftFin_zero k hk i₀
    have hsh_inj : ∀ m₁ < 2 * k + 1, ∀ m₂ < 2 * k + 1, sh m₁ = sh m₂ → m₁ = m₂ :=
      fun m₁ hm₁ m₂ hm₂ h => shiftFin_inj_of_lt k hk i₀ hm₁ hm₂ h
    have h_step : ∀ j : ℕ, ∃ a ∈ Uf (sh (2 * j + 1)), ∃ b ∈ Uf (sh (2 * j + 2)),
        G.ends (ef (sh (2 * j + 1))) = s(a, b) := by
      intro j
      obtain ⟨a, ha, b, hb, hab⟩ := hends (sh (2 * j + 1))
      have h_add : sh (2 * j + 1) + 1 = sh (2 * j + 2) := shiftFin_add_one k hk i₀ (2 * j + 1)
      rw [h_add] at hb
      exact ⟨a, ha, b, hb, hab⟩
    choose a_fn ha_fn b_fn hb_fn hab_fn using h_step
    let target : ℕ → V := fun m =>
      if m = 0 then u
      else if m % 2 = 1 then a_fn ((m - 1) / 2)
      else b_fn ((m - 1) / 2)
    have htarget_mem : ∀ m < 2 * k + 1, target m ∈ Uf (sh m) := by
      intro m hm
      dsimp [target]
      split_ifs with hm0 hmod
      · subst hm0
        rw [hsh0]
        exact hui₀
      · have h_eq : m = 2 * ((m - 1) / 2) + 1 := by omega
        have hUf_eq : Uf (sh m) = Uf (sh (2 * ((m - 1) / 2) + 1)) := congrArg (Uf ∘ sh) h_eq
        rw [hUf_eq]
        exact ha_fn ((m - 1) / 2)
      · have h_eq : m = 2 * ((m - 1) / 2) + 2 := by omega
        have hUf_eq : Uf (sh m) = Uf (sh (2 * ((m - 1) / 2) + 2)) := congrArg (Uf ∘ sh) h_eq
        rw [hUf_eq]
        exact hb_fn ((m - 1) / 2)
    have hex_sub : ∀ m : ℕ, m < 2 * k + 1 →
        ∃ MP_m : Finset E, MP_m ⊆ (induced G (Uf (sh m))).edges ∧ IsMatching G MP_m ∧
          (∀ w ∈ Uf (sh m), (PathsTreesFlowers.Duality.IsExposed G MP_m w ↔ w = target m)) :=
      fun m hm => ih (sh m) (target m) (htarget_mem m hm)
    choose MP_sub hMP_sub using hex_sub
    let MP_m : ℕ → Finset E := fun m => if hm : m < 2 * k + 1 then MP_sub m hm else ∅
    have hMP_m_props : ∀ m (hm : m < 2 * k + 1),
        MP_m m ⊆ (induced G (Uf (sh m))).edges ∧ IsMatching G (MP_m m) ∧
        (∀ w ∈ Uf (sh m), (PathsTreesFlowers.Duality.IsExposed G (MP_m m) w ↔ w = target m)) := by
      intro m hm
      dsimp [MP_m]
      rw [dif_pos hm]
      exact hMP_sub m hm
    set W := Finset.univ.biUnion Uf
    set A := (Finset.range (2 * k + 1)).biUnion MP_m
    set B := (Finset.range k).image (fun j => ef (sh (2 * j + 1)))
    set MP := A ∪ B
    have hW_eq : W = (Finset.range (2 * k + 1)).biUnion (fun m => Uf (sh m)) := by
      ext x
      simp only [W, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨i, hxi⟩
        obtain ⟨m, hm, rfl⟩ := shiftFin_surj k hk i₀ i
        exact ⟨m, hm, hxi⟩
      · rintro ⟨m, _, hxm⟩
        exact ⟨sh m, hxm⟩
    have hMP_sub_W : MP ⊆ (induced G W).edges := by
      intro e he
      simp only [induced, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_union.mp he with heA | heB
      · rcases Finset.mem_biUnion.mp heA with ⟨m, hm, hem⟩
        have hm_lt := Finset.mem_range.mp hm
        have he_sym2 := (Finset.mem_filter.mp ((hMP_m_props m hm_lt).1 hem)).2
        rw [Finset.mem_sym2_iff] at he_sym2 ⊢
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨sh m, Finset.mem_univ _, he_sym2 x hx⟩
      · rcases Finset.mem_image.mp heB with ⟨j, _, rfl⟩
        rw [hab_fn j, Finset.mk_mem_sym2_iff]
        exact ⟨Finset.mem_biUnion.mpr ⟨sh (2 * j + 1), Finset.mem_univ _, ha_fn j⟩,
          Finset.mem_biUnion.mpr ⟨sh (2 * j + 2), Finset.mem_univ _, hb_fn j⟩⟩
    have h_B_ends_in_Uf : ∀ j < k, ∀ m < 2 * k + 1, ∀ x ∈ Uf (sh m),
        x ∈ G.ends (ef (sh (2 * j + 1))) →
          (m = 2 * j + 1 ∧ x = target (2 * j + 1)) ∨
          (m = 2 * j + 2 ∧ x = target (2 * j + 2)) := by
      intro j hj m hm x hxm hxe
      rw [hab_fn j, Sym2.mem_iff] at hxe
      rcases hxe with rfl | rfl
      · have hm_eq : m = 2 * j + 1 := by
          by_contra hne
          have hsh_ne : sh m ≠ sh (2 * j + 1) :=
            fun h => hne (hsh_inj m hm (2 * j + 1) (by omega) h)
          exact Finset.disjoint_left.mp (hdisj (sh m) (sh (2 * j + 1)) hsh_ne) hxm (ha_fn j)
        subst hm_eq
        refine Or.inl ⟨rfl, ?_⟩
        change a_fn j = if 2 * j + 1 = 0 then u
          else if (2 * j + 1) % 2 = 1 then a_fn ((2 * j + 1 - 1) / 2)
          else b_fn ((2 * j + 1 - 1) / 2)
        have hne0 : 2 * j + 1 ≠ 0 := by omega
        have hmod1 : (2 * j + 1) % 2 = 1 := by omega
        have hdiv : (2 * j + 1 - 1) / 2 = j := by omega
        rw [if_neg hne0, if_pos hmod1, hdiv]
      · have hm_eq : m = 2 * j + 2 := by
          by_contra hne
          have hsh_ne : sh m ≠ sh (2 * j + 2) :=
            fun h => hne (hsh_inj m hm (2 * j + 2) (by omega) h)
          exact Finset.disjoint_left.mp (hdisj (sh m) (sh (2 * j + 2)) hsh_ne) hxm (hb_fn j)
        subst hm_eq
        refine Or.inr ⟨rfl, ?_⟩
        change b_fn j = if 2 * j + 2 = 0 then u
          else if (2 * j + 2) % 2 = 1 then a_fn ((2 * j + 2 - 1) / 2)
          else b_fn ((2 * j + 2 - 1) / 2)
        have hne0 : 2 * j + 2 ≠ 0 := by omega
        have hmod0 : (2 * j + 2) % 2 ≠ 1 := by omega
        have hdiv : (2 * j + 2 - 1) / 2 = j := by omega
        rw [if_neg hne0, if_neg hmod0, hdiv]
    have hMP_match : IsMatching G MP := by
      intro e₁ he₁ e₂ he₂ hne x hx₁ hx₂
      have hxW : x ∈ W := (induced G W).ends_mem e₁ (hMP_sub_W he₁) x hx₁
      rw [hW_eq] at hxW
      rcases Finset.mem_biUnion.mp hxW with ⟨m, hm_range, hxm⟩
      have hm_lt : m < 2 * k + 1 := Finset.mem_range.mp hm_range
      have h_e_in_m : ∀ e ∈ MP, x ∈ G.ends e →
          e ∈ MP_m m ∨ (∃ j < k, e = ef (sh (2 * j + 1)) ∧ x = target m ∧
            (m = 2 * j + 1 ∨ m = 2 * j + 2)) := by
        intro e he hxe
        rcases Finset.mem_union.mp he with heA | heB
        · rcases Finset.mem_biUnion.mp heA with ⟨m', hm'_range, hem'⟩
          have hm'_lt := Finset.mem_range.mp hm'_range
          have hxm' : x ∈ Uf (sh m') :=
            (induced G (Uf (sh m'))).ends_mem e ((hMP_m_props m' hm'_lt).1 hem') x hxe
          have hmm' : m' = m := by
            by_contra hne_m
            have hsh_ne : sh m' ≠ sh m := fun h => hne_m (hsh_inj m' hm'_lt m hm_lt h)
            exact Finset.disjoint_left.mp (hdisj (sh m') (sh m) hsh_ne) hxm' hxm
          exact Or.inl (hmm' ▸ hem')
        · rcases Finset.mem_image.mp heB with ⟨j, hj_range, rfl⟩
          have hj_lt := Finset.mem_range.mp hj_range
          rcases h_B_ends_in_Uf j hj_lt m hm_lt x hxm hxe with ⟨rfl, hx_t⟩ | ⟨rfl, hx_t⟩
          · exact Or.inr ⟨j, hj_lt, rfl, hx_t, Or.inl rfl⟩
          · exact Or.inr ⟨j, hj_lt, rfl, hx_t, Or.inr rfl⟩
      rcases h_e_in_m e₁ he₁ hx₁ with he₁_A | ⟨j₁, hj₁, rfl, hx_t₁, hm_j₁⟩ <;>
        rcases h_e_in_m e₂ he₂ hx₂ with he₂_A | ⟨j₂, hj₂, rfl, hx_t₂, hm_j₂⟩
      · exact (hMP_m_props m hm_lt).2.1 e₁ he₁_A e₂ he₂_A hne x hx₁ hx₂
      · exact ((hMP_m_props m hm_lt).2.2 x hxm).mpr hx_t₂ e₁ he₁_A hx₁
      · exact ((hMP_m_props m hm_lt).2.2 x hxm).mpr hx_t₁ e₂ he₂_A hx₂
      · have hj_eq : j₁ = j₂ := by omega
        exact hne (congrArg (fun j => ef (sh (2 * j + 1))) hj_eq)
    have hMP_exp : ∀ w ∈ W, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u) := by
      intro w hwW
      rw [hW_eq] at hwW
      rcases Finset.mem_biUnion.mp hwW with ⟨m, hm_range, hwm⟩
      have hm_lt : m < 2 * k + 1 := Finset.mem_range.mp hm_range
      constructor
      · intro hw_exp
        have hw_exp_m : PathsTreesFlowers.Duality.IsExposed G (MP_m m) w := by
          intro e he hwe
          exact hw_exp e (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨m, hm_range, he⟩)) hwe
        have hw_target : w = target m := ((hMP_m_props m hm_lt).2.2 w hwm).mp hw_exp_m
        by_cases hm0 : m = 0
        · subst hm0
          exact hw_target
        · exfalso
          by_cases hmod : m % 2 = 1
          · set j := (m - 1) / 2
            have hj_lt : j < k := by omega
            have hm_eq : 2 * j + 1 = m := by omega
            have he_B : ef (sh (2 * j + 1)) ∈ MP :=
              Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj_lt, rfl⟩)
            have hw_eq_a : w = a_fn j := by
              rw [hw_target]
              dsimp [target]
              rw [if_neg hm0, if_pos hmod]
            have hw_end : w ∈ G.ends (ef (sh (2 * j + 1))) := by
              rw [hab_fn j, hw_eq_a]
              exact Sym2.mem_mk_left _ _
            exact hw_exp (ef (sh (2 * j + 1))) he_B hw_end
          · set j := (m - 1) / 2
            have hj_lt : j < k := by omega
            have hm_eq : 2 * j + 2 = m := by omega
            have he_B : ef (sh (2 * j + 1)) ∈ MP :=
              Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj_lt, rfl⟩)
            have hw_eq_b : w = b_fn j := by
              rw [hw_target]
              dsimp [target]
              rw [if_neg hm0, if_neg hmod]
            have hw_end : w ∈ G.ends (ef (sh (2 * j + 1))) := by
              rw [hab_fn j, hw_eq_b]
              exact Sym2.mem_mk_right _ _
            exact hw_exp (ef (sh (2 * j + 1))) he_B hw_end
      · intro hwu
        subst w
        have hm0 : m = 0 := by
          by_contra hne0
          have hsh_ne : sh m ≠ sh 0 := fun h => hne0 (hsh_inj m hm_lt 0 (by omega) h)
          rw [hsh0] at hsh_ne
          exact Finset.disjoint_left.mp (hdisj (sh m) i₀ hsh_ne) hwm hui₀
        subst hm0
        intro e he hue
        rcases Finset.mem_union.mp he with heA | heB
        · rcases Finset.mem_biUnion.mp heA with ⟨m', hm'_range, hem'⟩
          have hm'_lt := Finset.mem_range.mp hm'_range
          have hum' : u ∈ Uf (sh m') :=
            (induced G (Uf (sh m'))).ends_mem e ((hMP_m_props m' hm'_lt).1 hem') u hue
          have hm'0 : m' = 0 := by
            by_contra hne0
            have hsh_ne : sh m' ≠ sh 0 := fun h => hne0 (hsh_inj m' hm'_lt 0 (by omega) h)
            exact Finset.disjoint_left.mp (hdisj (sh m') (sh 0) hsh_ne) hum' hwm
          subst hm'0
          exact ((hMP_m_props 0 (by omega)).2.2 u hwm).mpr rfl e hem' hue
        · rcases Finset.mem_image.mp heB with ⟨j, hj_range, rfl⟩
          have hj_lt := Finset.mem_range.mp hj_range
          rcases h_B_ends_in_Uf j hj_lt 0 (by omega) u hwm hue with ⟨h1, _⟩ | ⟨h2, _⟩ <;> omega
    exact ⟨MP, hMP_sub_W, hMP_match, hMP_exp⟩

/-! ### Part 3: Partition relation between `P₁` and `P₂` and lifting `MP ∪ M₂` -/

lemma part_P₁_eq_singleton_of_mem_U {P₁ P₂ : Finpartition (Finset.univ : Finset V)}
    {U : Finset V} (hP : P₁.parts = P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)))
    {x : V} (hxU : x ∈ U) : P₁.part x = {x} := by
  have h_mem : ({x} : Finset V) ∈ P₁.parts := by
    rw [hP]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hxU, rfl⟩)
  exact P₁.eq_of_mem_parts (P₁.part_mem.2 (Finset.mem_univ x)) h_mem
    (P₁.mem_part (Finset.mem_univ x)) (Finset.mem_singleton_self x)

lemma part_P₁_eq_part_P₂_of_not_mem_U {P₁ P₂ : Finpartition (Finset.univ : Finset V)}
    {U : Finset V} (hP : P₁.parts = P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)))
    {x : V} (hxU : x ∉ U) : P₁.part x = P₂.part x := by
  have hx_ne : P₂.part x ≠ U := fun h => hxU (h ▸ P₂.mem_part (Finset.mem_univ x))
  have h_mem : P₂.part x ∈ P₁.parts := by
    rw [hP]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hx_ne, P₂.part_mem.2 (Finset.mem_univ x)⟩)
  exact P₁.eq_of_mem_parts (P₁.part_mem.2 (Finset.mem_univ x)) h_mem
    (P₁.mem_part (Finset.mem_univ x)) (P₂.mem_part (Finset.mem_univ x))

lemma part_P₁_sub_part_P₂ {P₁ P₂ : Finpartition (Finset.univ : Finset V)}
    {U : Finset V} (hU : U ∈ P₂.parts)
    (hP : P₁.parts = P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)))
    (x : V) : P₁.part x ⊆ P₂.part x := by
  by_cases hxU : x ∈ U
  · rw [part_P₁_eq_singleton_of_mem_U hP hxU, Finset.singleton_subset_iff]
    have h_eq : P₂.part x = U :=
      P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x)) hU
        (P₂.mem_part (Finset.mem_univ x)) hxU
    exact h_eq ▸ hxU
  · rw [part_P₁_eq_part_P₂_of_not_mem_U hP hxU]

lemma lift_matching_to_P₁ {G : EdmondsMatching65.Polyhedron.Graph V E}
    {P₁ P₂ : Finpartition (Finset.univ : Finset V)} {U : Finset V} (hU : U ∈ P₂.parts)
    (hP : P₁.parts = P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)))
    {M₂ : Finset (ShrinkE G P₂)} (hM₂ : IsMatching (shrink G P₂) M₂)
    {MP : Finset E} (hMP_sub : MP ⊆ (induced G U).edges) (hMP : IsMatching G MP)
    {u : V} (_huU : u ∈ U)
    (hMP_exp : ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u))
    (hM₂_u : ∀ e ∈ M₂, ∀ x ∈ U, x ∈ G.ends e.1 → x = u) :
    ∃ M₁ : Finset (ShrinkE G P₁), IsMatching (shrink G P₁) M₁ ∧
      M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _) := by
  set S := MP ∪ M₂.map (Function.Embedding.subtype _)
  have hS_not_diag : ∀ e ∈ S, ¬ ((G.ends e).map (partOf P₁)).IsDiag := by
    intro e he hdiag
    rcases Sym2.exists.mp ⟨G.ends e, rfl⟩ with ⟨a, b, hab⟩
    have hne : a ≠ b := by
      rintro rfl
      exact G.loopless e (hab ▸ Sym2.mk_isDiag_iff.mpr rfl)
    rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff] at hdiag
    have hpart_eq : P₁.part a = P₁.part b := congrArg Subtype.val hdiag
    rcases Finset.mem_union.mp he with heMP | heM₂
    · have heU := (Finset.mem_filter.mp (hMP_sub heMP)).2
      rw [hab, Finset.mk_mem_sym2_iff] at heU
      rw [part_P₁_eq_singleton_of_mem_U hP heU.1,
        part_P₁_eq_singleton_of_mem_U hP heU.2,
        Finset.singleton_inj] at hpart_eq
      exact hne hpart_eq
    · rcases Finset.mem_map.mp heM₂ with ⟨f, _, rfl⟩
      apply f.2
      change G.ends f.1 = s(a, b) at hab
      rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
      have ha_in_b : a ∈ P₂.part b :=
        part_P₁_sub_part_P₂ hU hP b (hpart_eq ▸ P₁.mem_part (Finset.mem_univ a))
      exact Subtype.ext (P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ a))
        (P₂.part_mem.2 (Finset.mem_univ b)) (P₂.mem_part (Finset.mem_univ a)) ha_in_b)
  set M₁ : Finset (ShrinkE G P₁) :=
    S.subtype (fun e => ¬ ((G.ends e).map (partOf P₁)).IsDiag)
  have hM₁_map : M₁.map (Function.Embedding.subtype _) = S := by
    ext e
    simp only [M₁, Finset.mem_map, Finset.mem_subtype, Function.Embedding.coe_subtype,
      Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
    exact hS_not_diag e
  refine ⟨M₁, ?_, hM₁_map⟩
  intro f₁ hf₁ f₂ hf₂ hne q hq₁ hq₂
  have hf₁S : f₁.1 ∈ S := Finset.mem_subtype.mp hf₁
  have hf₂S : f₂.1 ∈ S := Finset.mem_subtype.mp hf₂
  have hf_ne_val : f₁.1 ≠ f₂.1 := Subtype.coe_ne_coe.mpr hne
  change q ∈ (G.ends f₁.1).map (partOf P₁) at hq₁
  change q ∈ (G.ends f₂.1).map (partOf P₁) at hq₂
  rcases Sym2.mem_map.mp hq₁ with ⟨x₁, hx₁e, hx₁q⟩
  rcases Sym2.mem_map.mp hq₂ with ⟨x₂, hx₂e, hx₂q⟩
  have hx₁_mem : x₁ ∈ q.1 := by
    rw [← congrArg Subtype.val hx₁q]
    exact P₁.mem_part (Finset.mem_univ x₁)
  have hx₂_mem : x₂ ∈ q.1 := by
    rw [← congrArg Subtype.val hx₂q]
    exact P₁.mem_part (Finset.mem_univ x₂)
  have hq_mem : q.1 ∈ P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)) := hP ▸ q.2
  rcases Finset.mem_union.mp hq_mem with hq_erase | hq_img
  · rcases Finset.mem_erase.mp hq_erase with ⟨hq_ne_U, hq_P₂⟩
    have hdisj_qU : Disjoint q.1 U := P₂.disjoint hq_P₂ hU hq_ne_U
    have hf₁_not_MP : f₁.1 ∉ MP := by
      intro hf₁MP
      have hx₁U : x₁ ∈ U := (induced G U).ends_mem f₁.1 (hMP_sub hf₁MP) x₁ hx₁e
      exact Finset.disjoint_left.mp hdisj_qU hx₁_mem hx₁U
    have hf₂_not_MP : f₂.1 ∉ MP := by
      intro hf₂MP
      have hx₂U : x₂ ∈ U := (induced G U).ends_mem f₂.1 (hMP_sub hf₂MP) x₂ hx₂e
      exact Finset.disjoint_left.mp hdisj_qU hx₂_mem hx₂U
    rcases (Finset.mem_union.mp hf₁S).resolve_left hf₁_not_MP with h₁_map
    rcases (Finset.mem_union.mp hf₂S).resolve_left hf₂_not_MP with h₂_map
    rcases Finset.mem_map.mp h₁_map with ⟨g₁, hg₁, hg₁_eq⟩
    rcases Finset.mem_map.mp h₂_map with ⟨g₂, hg₂, hg₂_eq⟩
    change g₁.1 = f₁.1 at hg₁_eq
    change g₂.1 = f₂.1 at hg₂_eq
    have hg_ne : g₁ ≠ g₂ := fun h =>
      hf_ne_val (hg₁_eq.symm.trans ((congrArg Subtype.val h).trans hg₂_eq))
    have hq_P₂_₁ : (⟨q.1, hq_P₂⟩ : {W // W ∈ P₂.parts}) ∈ (shrink G P₂).ends g₁ := by
      change (⟨q.1, hq_P₂⟩ : {W // W ∈ P₂.parts}) ∈ (G.ends g₁.1).map (partOf P₂)
      rw [hg₁_eq]
      refine Sym2.mem_map.mpr ⟨x₁, hx₁e, Subtype.ext ?_⟩
      exact P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x₁)) hq_P₂
        (P₂.mem_part (Finset.mem_univ x₁)) hx₁_mem
    have hq_P₂_₂ : (⟨q.1, hq_P₂⟩ : {W // W ∈ P₂.parts}) ∈ (shrink G P₂).ends g₂ := by
      change (⟨q.1, hq_P₂⟩ : {W // W ∈ P₂.parts}) ∈ (G.ends g₂.1).map (partOf P₂)
      rw [hg₂_eq]
      refine Sym2.mem_map.mpr ⟨x₂, hx₂e, Subtype.ext ?_⟩
      exact P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x₂)) hq_P₂
        (P₂.mem_part (Finset.mem_univ x₂)) hx₂_mem
    exact hM₂ g₁ hg₁ g₂ hg₂ hg_ne ⟨q.1, hq_P₂⟩ hq_P₂_₁ hq_P₂_₂
  · rcases Finset.mem_image.mp hq_img with ⟨x, hxU, hqx⟩
    have hx₁_eq : x₁ = x := Finset.mem_singleton.mp (hqx ▸ hx₁_mem)
    have hx₂_eq : x₂ = x := Finset.mem_singleton.mp (hqx ▸ hx₂_mem)
    rw [hx₁_eq] at hx₁e
    rw [hx₂_eq] at hx₂e
    rcases Finset.mem_union.mp hf₁S with hf₁MP | hf₁M₂ <;>
      rcases Finset.mem_union.mp hf₂S with hf₂MP | hf₂M₂
    · exact hMP f₁.1 hf₁MP f₂.1 hf₂MP hf_ne_val x hx₁e hx₂e
    · rcases Finset.mem_map.mp hf₂M₂ with ⟨g₂, hg₂, hg₂_eq⟩
      change g₂.1 = f₂.1 at hg₂_eq
      have hx_u : x = u := hM₂_u g₂ hg₂ x hxU (hg₂_eq.symm ▸ hx₂e)
      exact (hMP_exp x hxU).mpr hx_u f₁.1 hf₁MP hx₁e
    · rcases Finset.mem_map.mp hf₁M₂ with ⟨g₁, hg₁, hg₁_eq⟩
      change g₁.1 = f₁.1 at hg₁_eq
      have hx_u : x = u := hM₂_u g₁ hg₁ x hxU (hg₁_eq.symm ▸ hx₁e)
      exact (hMP_exp x hxU).mpr hx_u f₂.1 hf₂MP hx₂e
    · rcases Finset.mem_map.mp hf₁M₂ with ⟨g₁, hg₁, hg₁_eq⟩
      rcases Finset.mem_map.mp hf₂M₂ with ⟨g₂, hg₂, hg₂_eq⟩
      change g₁.1 = f₁.1 at hg₁_eq
      change g₂.1 = f₂.1 at hg₂_eq
      have hg_ne : g₁ ≠ g₂ := fun h =>
        hf_ne_val (hg₁_eq.symm.trans ((congrArg Subtype.val h).trans hg₂_eq))
      have hU_g₁ : (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (shrink G P₂).ends g₁ := by
        change (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (G.ends g₁.1).map (partOf P₂)
        rw [hg₁_eq]
        refine Sym2.mem_map.mpr ⟨x, hx₁e, Subtype.ext ?_⟩
        exact P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x)) hU
          (P₂.mem_part (Finset.mem_univ x)) hxU
      have hU_g₂ : (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (shrink G P₂).ends g₂ := by
        change (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (G.ends g₂.1).map (partOf P₂)
        rw [hg₂_eq]
        refine Sym2.mem_map.mpr ⟨x, hx₂e, Subtype.ext ?_⟩
        exact P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x)) hU
          (P₂.mem_part (Finset.mem_univ x)) hxU
      exact hM₂ g₁ hg₁ g₂ hg₂ hg_ne ⟨U, hU⟩ hU_g₁ hU_g₂

/-! ### Part 4: Main theorem `lemma_4_14_expansion` -/

theorem lemma_4_14_expansion {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P₁ P₂ : Finpartition (Finset.univ : Finset V)) (U : Finset V) (hU : U ∈ P₂.parts)
    (hodd : IsOddCircuitSet G U)
    (hP : P₁.parts = P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)))
    (M₂ : Finset (ShrinkE G P₂)) (hM₂ : IsMatching (shrink G P₂) M₂) :
    (∃ MP : Finset E, MP ⊆ (induced G U).edges ∧ IsMatching G MP ∧
      (∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
      ∃ M₁ : Finset (ShrinkE G P₁), IsMatching (shrink G P₁) M₁ ∧
        M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _)) ∧
    ((∀ e ∈ M₂, (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∉ (shrink G P₂).ends e) →
      ∀ u ∈ U, ∃ MP : Finset E, MP ⊆ (induced G U).edges ∧ IsMatching G MP ∧
        (∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
        ∃ M₁ : Finset (ShrinkE G P₁), IsMatching (shrink G P₁) M₁ ∧
          M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _)) := by
  have h_second : (∀ e ∈ M₂, (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∉ (shrink G P₂).ends e) →
      ∀ u ∈ U, ∃ MP : Finset E, MP ⊆ (induced G U).edges ∧ IsMatching G MP ∧
        (∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
        ∃ M₁ : Finset (ShrinkE G P₁), IsMatching (shrink G P₁) M₁ ∧
          M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _) := by
    intro h_no_edge u huU
    obtain ⟨MP, hMP_sub, hMP_match, hMP_exp⟩ := oddCircuitSet_matching_any_exposed hodd u huU
    have hM₂_u : ∀ e ∈ M₂, ∀ x ∈ U, x ∈ G.ends e.1 → x = u := by
      intro e he x hxU hxe
      exfalso
      refine h_no_edge e he ?_
      change (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (G.ends e.1).map (partOf P₂)
      refine Sym2.mem_map.mpr ⟨x, hxe, Subtype.ext ?_⟩
      exact P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x)) hU
        (P₂.mem_part (Finset.mem_univ x)) hxU
    obtain ⟨M₁, hM₁_match, hM₁_map⟩ :=
      lift_matching_to_P₁ hU hP hM₂ hMP_sub hMP_match huU hMP_exp hM₂_u
    exact ⟨MP, hMP_sub, hMP_match, hMP_exp, M₁, hM₁_match, hM₁_map⟩
  refine ⟨?_, h_second⟩
  by_cases hex_e : ∃ e ∈ M₂, (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (shrink G P₂).ends e
  · rcases hex_e with ⟨e₀, he₀M₂, he₀_end⟩
    change (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (G.ends e₀.1).map (partOf P₂) at he₀_end
    rcases Sym2.mem_map.mp he₀_end with ⟨u, hue₀, hu_part⟩
    have hpu : P₂.part u = U := congrArg Subtype.val hu_part
    have huU : u ∈ U := hpu ▸ P₂.mem_part (Finset.mem_univ u)
    obtain ⟨MP, hMP_sub, hMP_match, hMP_exp⟩ := oddCircuitSet_matching_any_exposed hodd u huU
    have hM₂_u : ∀ e ∈ M₂, ∀ x ∈ U, x ∈ G.ends e.1 → x = u := by
      intro e he x hxU hxe
      have he_end : (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (shrink G P₂).ends e := by
        change (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∈ (G.ends e.1).map (partOf P₂)
        refine Sym2.mem_map.mpr ⟨x, hxe, Subtype.ext ?_⟩
        exact P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x)) hU
          (P₂.mem_part (Finset.mem_univ x)) hxU
      have hee₀ : e = e₀ := by
        by_contra hne
        exact hM₂ e he e₀ he₀M₂ hne ⟨U, hU⟩ he_end he₀_end
      subst hee₀
      have hpx : P₂.part x = U :=
        P₂.eq_of_mem_parts (P₂.part_mem.2 (Finset.mem_univ x)) hU
          (P₂.mem_part (Finset.mem_univ x)) hxU
      rcases Sym2.exists.mp ⟨G.ends e.1, rfl⟩ with ⟨a, b, hab⟩
      have hx_ab : x = a ∨ x = b := by rw [hab, Sym2.mem_iff] at hxe; exact hxe
      have hu_ab : u = a ∨ u = b := by rw [hab, Sym2.mem_iff] at hue₀; exact hue₀
      rcases hx_ab with rfl | rfl <;> rcases hu_ab with rfl | rfl
      · rfl
      · exfalso
        apply e.2
        rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
        exact Subtype.ext (hpx.trans hpu.symm)
      · exfalso
        apply e.2
        rw [hab, Sym2.map_mk, Sym2.mk_isDiag_iff]
        exact Subtype.ext (hpu.trans hpx.symm)
      · rfl
    obtain ⟨M₁, hM₁_match, hM₁_map⟩ :=
      lift_matching_to_P₁ hU hP hM₂ hMP_sub hMP_match huU hMP_exp hM₂_u
    exact ⟨MP, hMP_sub, hMP_match, ⟨u, huU, hMP_exp⟩, M₁, hM₁_match, hM₁_map⟩
  · simp only [not_exists, not_and] at hex_e
    obtain ⟨u, huU⟩ := P₂.nonempty_of_mem_parts hU
    obtain ⟨MP, hMP_sub, hMP_match, hMP_exp, M₁, hM₁_match, hM₁_map⟩ := h_second hex_e u huU
    exact ⟨MP, hMP_sub, hMP_match, ⟨u, huU, hMP_exp⟩, M₁, hM₁_match, hM₁_map⟩

end SolPathsTreesFlowersLemma414Expansion

theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E)
    (P₁ P₂ : Finpartition (Finset.univ : Finset V)) (U : Finset V) (hU : U ∈ P₂.parts)
    (hodd : PathsTreesFlowers.Invariance.IsOddCircuitSet G U)
    (hP : P₁.parts = P₂.parts.erase U ∪ U.image (fun u => ({u} : Finset V)))
    (M₂ : Finset (PathsTreesFlowers.Invariance.ShrinkE G P₂))
    (hM₂ : EdmondsMatching65.Polyhedron.IsMatching (PathsTreesFlowers.Invariance.shrink G P₂) M₂) :
    (∃ MP : Finset E, MP ⊆ (PathsTreesFlowers.Invariance.induced G U).edges ∧
      EdmondsMatching65.Polyhedron.IsMatching G MP ∧
      (∃ u ∈ U, ∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
      ∃ M₁ : Finset (PathsTreesFlowers.Invariance.ShrinkE G P₁),
        EdmondsMatching65.Polyhedron.IsMatching (PathsTreesFlowers.Invariance.shrink G P₁) M₁ ∧
        M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _)) ∧
    ((∀ e ∈ M₂, (⟨U, hU⟩ : {W // W ∈ P₂.parts}) ∉
        (PathsTreesFlowers.Invariance.shrink G P₂).ends e) →
      ∀ u ∈ U, ∃ MP : Finset E, MP ⊆ (PathsTreesFlowers.Invariance.induced G U).edges ∧
        EdmondsMatching65.Polyhedron.IsMatching G MP ∧
        (∀ w ∈ U, (PathsTreesFlowers.Duality.IsExposed G MP w ↔ w = u)) ∧
        ∃ M₁ : Finset (PathsTreesFlowers.Invariance.ShrinkE G P₁),
          EdmondsMatching65.Polyhedron.IsMatching (PathsTreesFlowers.Invariance.shrink G P₁) M₁ ∧
          M₁.map (Function.Embedding.subtype _) = MP ∪ M₂.map (Function.Embedding.subtype _)) :=
  SolPathsTreesFlowersLemma414Expansion.lemma_4_14_expansion G P₁ P₂ U hU hodd hP M₂ hM₂
