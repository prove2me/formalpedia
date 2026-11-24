-- Prove2me | solution 1 for WeightedEdgeColor.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:34:02.810887+00:00
-- url     : https://prove2.me/submissions/9e948b77-e0d4-4e42-8d5b-aa1d6d81563c

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph
import Definitions.Def_WeightedEdgeColor_WGraph_IsProperColoring

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WECLemmaA1
open WeightedEdgeColor WeightedEdgeColor.WGraph

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Load of colour `c` at `x` among the edges of `F`. -/
noncomputable def load (J : WGraph V E) {K : ℕ} (φ : E → Fin K) (F : Finset E) (x : V) (c : Fin K) : ℝ :=
  ∑ f ∈ F.filter (fun f => x ∈ J.ends f ∧ φ f = c), J.w f

theorem load_nonneg (J : WGraph V E) {K : ℕ} (φ : E → Fin K) (F : Finset E) (x : V) (c : Fin K) :
    0 ≤ load J φ F x c :=
  Finset.sum_nonneg (fun f _ => (J.w_pos f).le)

theorem sum_load (J : WGraph V E) {K : ℕ} (φ : E → Fin K) (F : Finset E) (x : V) :
    ∑ c, load J φ F x c = ∑ f ∈ F.filter (fun f => x ∈ J.ends f), J.w f := by
  unfold load
  rw [← Finset.sum_fiberwise (F.filter (fun f => x ∈ J.ends f)) φ]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.filter_filter]

/-- If colour `c` is blocked at `x` for an edge of weight `a ≤` all weights in `F`, the load is
at least `1/2`. -/
theorem half_le_load (J : WGraph V E) {K : ℕ} (φ : E → Fin K) (F : Finset E) (x : V) (c : Fin K)
    (a : ℝ) (ha1 : a ≤ 1) (hmin : ∀ f ∈ F, a ≤ J.w f) (hbl : 1 < load J φ F x c + a) :
    1 / 2 ≤ load J φ F x c := by
  by_cases h2 : 1 / 2 ≤ a
  · -- the load is positive, so some edge is present, with weight ≥ a
    have hpos : 0 < load J φ F x c := by linarith
    unfold load at hpos ⊢
    obtain ⟨f, hf, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    have hle : J.w f ≤ ∑ f ∈ F.filter (fun f => x ∈ J.ends f ∧ φ f = c), J.w f :=
      Finset.single_le_sum (f := J.w) (fun g _ => (J.w_pos g).le) hf
    have := hmin f (Finset.mem_filter.mp hf).1
    linarith
  · push Not at h2; linarith

theorem load_update (J : WGraph V E) {K : ℕ} (φ : E → Fin K) (F : Finset E) (e : E) (he : e ∉ F)
    (c : Fin K) (x : V) (d : Fin K) :
    load J (Function.update φ e c) (insert e F) x d =
      load J φ F x d + (if x ∈ J.ends e ∧ c = d then J.w e else 0) := by
  unfold load
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_insert he]
  simp only [Function.update_self]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  have hfe : f ≠ e := fun h => he (h ▸ hf)
  simp [Function.update_of_ne hfe]

theorem blocked_card (J : WGraph V E) {K : ℕ} (φ : E → Fin K) (F : Finset E) (e : E) (he : e ∉ F)
    (x : V) (hx : x ∈ J.ends e) (R : ℝ) (hR : J.W x ≤ R) (hmin : ∀ f ∈ F, J.w e ≤ J.w f) :
    ((Finset.univ.filter (fun c => 1 < load J φ F x c + J.w e)).card : ℝ) < 2 * R := by
  set Bx := Finset.univ.filter (fun c => 1 < load J φ F x c + J.w e)
  have h1 : (Bx.card : ℝ) * (1 / 2) ≤ ∑ c ∈ Bx, load J φ F x c := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c hc
    simp only [Nat.cast_one, one_mul]
    exact half_le_load J φ F x c (J.w e) (J.w_le_one e) hmin (Finset.mem_filter.mp hc).2
  have h2 : ∑ c ∈ Bx, load J φ F x c ≤ ∑ c, load J φ F x c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ => load_nonneg J φ F x c)
  have h3 : ∑ f ∈ F.filter (fun f => x ∈ J.ends f), J.w f + J.w e ≤ J.W x := by
    unfold WGraph.W WGraph.inc
    have hsub : insert e (F.filter (fun f => x ∈ J.ends f)) ⊆ Finset.univ.filter (fun f => x ∈ J.ends f) := by
      intro f hf
      rcases Finset.mem_insert.mp hf with h | h
      · subst h; simp [hx]
      · simp [(Finset.mem_filter.mp h).2]
    have hnot : e ∉ F.filter (fun f => x ∈ J.ends f) := fun h => he (Finset.mem_filter.mp h).1
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f _ _ => (J.w_pos f).le)
    rw [Finset.sum_insert hnot] at this
    linarith
  rw [sum_load] at h2
  have := J.w_pos e
  linarith

theorem greedy (J : WGraph V E) (R : ℝ) (hR : ∀ v, J.W v ≤ R) :
    ∀ (n : ℕ) (F : Finset E), F.card = n →
      ∃ φ : E → Fin (⌊4 * R⌋₊ + 1), ∀ x c, load J φ F x c ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro F hF
    rw [Finset.card_eq_zero] at hF
    subst hF
    exact ⟨fun _ => 0, fun x c => by simp [load]⟩
  | succ n ih =>
    intro F hF
    have hne : F.Nonempty := by rw [← Finset.card_pos, hF]; omega
    obtain ⟨e, heF, hmin⟩ := F.exists_min_image J.w hne
    set F' := F.erase e
    have hF' : F'.card = n := by rw [Finset.card_erase_of_mem heF, hF]; rfl
    have heF' : e ∉ F' := Finset.notMem_erase e F
    have hmin' : ∀ f ∈ F', J.w e ≤ J.w f := fun f hf => hmin f (Finset.mem_of_mem_erase hf)
    obtain ⟨φ', hφ'⟩ := ih F' hF'
    obtain ⟨⟨u, v⟩, hp⟩ := Quot.exists_rep (J.ends e)
    change s(u, v) = J.ends e at hp
    have hu : u ∈ J.ends e := by rw [← hp]; exact Sym2.mem_mk_left u v
    have hv : v ∈ J.ends e := by rw [← hp]; exact Sym2.mem_mk_right u v
    set Bu := Finset.univ.filter (fun c => 1 < load J φ' F' u c + J.w e)
    set Bv := Finset.univ.filter (fun c => 1 < load J φ' F' v c + J.w e)
    have hBu := blocked_card J φ' F' e heF' u hu R (hR u) hmin'
    have hBv := blocked_card J φ' F' e heF' v hv R (hR v) hmin'
    have hfl : 4 * R < (⌊4 * R⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    obtain ⟨c, hc⟩ : ∃ c, c ∉ Bu ∪ Bv := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin (⌊4 * R⌋₊ + 1))) ⊆ Bu ∪ Bv := fun c _ => hall c
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le Bu Bv
      simp only [Finset.card_univ, Fintype.card_fin] at h1
      have h3 : ((⌊4 * R⌋₊ + 1 : ℕ) : ℝ) ≤ (Bu.card : ℝ) + Bv.card := by exact_mod_cast h1.trans h2
      push_cast at h3
      linarith
    have hcu : load J φ' F' u c + J.w e ≤ 1 := by
      have : c ∉ Bu := fun h => hc (Finset.mem_union_left _ h)
      simpa [Bu] using this
    have hcv : load J φ' F' v c + J.w e ≤ 1 := by
      have : c ∉ Bv := fun h => hc (Finset.mem_union_right _ h)
      simpa [Bv] using this
    refine ⟨Function.update φ' e c, fun x d => ?_⟩
    have hFins : F = insert e F' := (Finset.insert_erase heF).symm
    rw [hFins, load_update J φ' F' e heF' c x d]
    split_ifs with h
    · obtain ⟨hx, rfl⟩ := h
      rw [← hp, Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact hcu
      · exact hcv
    · simpa using hφ' x d

end WECLemmaA1

open WeightedEdgeColor WeightedEdgeColor.WGraph WECLemmaA1 in
theorem solution (V E : Type) [Fintype V] [DecidableEq V] [Fintype E]
    (J : WGraph V E) (R : ℝ) (hR : ∀ v, J.W v ≤ R) :
    ∃ φ : E → Fin (⌊4 * R⌋₊ + 1), J.IsProperColoring φ := by
  classical
  obtain ⟨φ, hφ⟩ := greedy J R hR (Finset.univ : Finset E).card Finset.univ rfl
  refine ⟨φ, fun v c => ?_⟩
  have := hφ v c
  unfold load at this
  unfold WGraph.inc
  rw [Finset.filter_filter]
  exact this
