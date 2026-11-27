-- Prove2me | solution 1 for SPFacilityGraph.attribution_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:52:16.812285+00:00
-- url     : https://prove2.me/submissions/84c31269-c7c3-4165-970c-eb6cc05507d9

import Mathlib
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_le_walk
import Theorems.Thm_SPFacilityGraph_MetricGraph_exists_walk_eq_dist
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_triangle
import Theorems.Thm_SPFacilityGraph_MetricGraph_dist_comm
import Definitions.Def_SPFacilityGraph_IsEdgeTriangulation
import Definitions.Def_SPFacilityGraph_HasDetAttribution

set_option autoImplicit false


namespace SPFGKuhn

open Finset

/-- convex hull of an injective image of a finite index set, in terms of indexed weights -/
lemma mem_convexHull_image_iff {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    [DecidableEq V] (v : ι → V) (hv : Function.Injective v) (S : Finset ι) (p : V) :
    p ∈ convexHull ℝ ((S.image v : Finset V) : Set V) ↔
      ∃ w : ι → ℝ, (∀ l, 0 ≤ w l) ∧ (∀ l, l ∉ S → w l = 0) ∧ ∑ l, w l = 1 ∧
        ∑ l, w l • v l = p := by
  constructor
  · rw [Finset.mem_convexHull]
    rintro ⟨w, hw0, hw1, hwc⟩
    refine ⟨fun l => if l ∈ S then w (v l) else 0, ?_, ?_, ?_, ?_⟩
    · intro l; dsimp only; split_ifs with h
      · exact hw0 _ (Finset.mem_image_of_mem v h)
      · exact le_rfl
    · intro l hl; simp [hl]
    · rw [← hw1, Finset.sum_image (fun a _ b _ h => hv h), ← Finset.sum_filter]; simp
    · rw [← hwc, Finset.centerMass, hw1, inv_one, one_smul, Finset.sum_image (fun a _ b _ h => hv h)]
      simp only [ite_smul, zero_smul, id]
      rw [← Finset.sum_filter]; simp
  · rintro ⟨w, hw0, hwS, hw1, hwp⟩
    have hS : ∑ l ∈ S, w l = 1 := by
      rw [← hw1]; exact Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => hwS l hl)
    have : S.centerMass w v = p := by
      rw [Finset.centerMass, hS, inv_one, one_smul, ← hwp]
      exact Finset.sum_subset (Finset.subset_univ S) (fun l _ hl => by rw [hwS l hl, zero_smul])
    rw [← this]
    apply Finset.centerMass_mem_convexHull S (fun l _ => hw0 l) (by rw [hS]; exact one_pos)
    intro l hl; exact Finset.mem_coe.2 (Finset.mem_image_of_mem v hl)

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- Kuhn vertex `l` of the box `∏ [β j .1, β j .2]` for the permutation `σ`. -/
def kv (β : Fin n → V × V) (σ : Equiv.Perm (Fin n)) (l : Fin (n+1)) : Fin n → V :=
  fun j => if ((σ.symm j : Fin n) : ℕ) < (l : ℕ) then (β j).2 else (β j).1

/-- tail sum of weights -/
def tailw (w : Fin (n+1) → ℝ) (m : ℕ) : ℝ := ∑ l : Fin (n+1), if m < (l : ℕ) then w l else 0

lemma sum_smul_kv (β : Fin n → V × V) (σ : Equiv.Perm (Fin n)) (w : Fin (n+1) → ℝ) (j : Fin n) :
    (∑ l, w l • kv β σ l) j =
      (∑ l, w l) • (β j).1 + tailw w (σ.symm j) • ((β j).2 - (β j).1) := by
  rw [Finset.sum_apply, tailw, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Pi.smul_apply, kv]
  split_ifs with h
  · rw [smul_sub, add_sub_cancel]
  · simp

lemma tailw_eq (w : Fin (n+1) → ℝ) (m : ℕ) (hm : m + 1 < n + 1) :
    tailw w m = w ⟨m + 1, hm⟩ + tailw w (m + 1) := by
  have : tailw w m - tailw w (m + 1) = w ⟨m + 1, hm⟩ := by
    unfold tailw
    rw [← Finset.sum_sub_distrib]
    have : ∀ l : Fin (n+1), ((if m < (l:ℕ) then w l else 0) - if m + 1 < (l:ℕ) then w l else 0) =
        if l = ⟨m + 1, hm⟩ then w l else 0 := by
      intro l
      by_cases h1 : (l : ℕ) = m + 1
      · have : l = ⟨m + 1, hm⟩ := Fin.ext h1
        subst this; simp
      · have hne : l ≠ ⟨m + 1, hm⟩ := fun h => h1 (by rw [h])
        by_cases h2 : m < (l : ℕ)
        · simp [h2, show m + 1 < (l:ℕ) by omega, hne]
        · simp [h2, show ¬ (m + 1 < (l:ℕ)) by omega, hne]
    rw [Finset.sum_congr rfl (fun l _ => this l), Finset.sum_ite_eq']
    simp
  linarith

lemma tailw_ge (w : Fin (n+1) → ℝ) (m : ℕ) (hm : n ≤ m) : tailw w m = 0 := by
  unfold tailw
  apply Finset.sum_eq_zero
  intro l _
  have := l.2
  simp [show ¬ (m < (l:ℕ)) by omega]

lemma tailw_zero_eq (w : Fin (n+1) → ℝ) : tailw w 0 = ∑ l, w l - w 0 := by
  have : (∑ l, w l) - tailw w 0 = w 0 := by
    unfold tailw
    rw [← Finset.sum_sub_distrib]
    have : ∀ l : Fin (n+1), (w l - if 0 < (l:ℕ) then w l else 0) = if l = 0 then w l else 0 := by
      intro l
      by_cases h : l = 0
      · subst h; simp
      · have : 0 < (l : ℕ) := by
          rcases Nat.eq_zero_or_pos (l : ℕ) with h' | h'
          · exact absurd (Fin.ext h') h
          · exact h'
        simp [h, this]
    rw [Finset.sum_congr rfl (fun l _ => this l), Finset.sum_ite_eq']
    simp
  linarith

lemma tailw_anti (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 ≤ w l) {m m' : ℕ} (h : m ≤ m') :
    tailw w m' ≤ tailw w m := by
  unfold tailw
  apply Finset.sum_le_sum
  intro l _
  by_cases h1 : m' < (l : ℕ)
  · simp [h1, show m < (l : ℕ) by omega]
  · simp only [h1, if_false]; split_ifs <;> simp [hw]

lemma tailw_ge_add (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 ≤ w l) (m : ℕ) (l : Fin (n+1))
    (h : m < (l : ℕ)) : w l + tailw w l ≤ tailw w m := by
  unfold tailw
  have : w l = ∑ l' : Fin (n+1), if l' = l then w l' else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l' _
  by_cases h1 : l' = l
  · subst h1; simp [h]
  · by_cases h2 : (l : ℕ) < (l' : ℕ)
    · simp [h1, h2, show m < (l' : ℕ) by omega]
    · simp only [h1, h2, if_false, add_zero]; split_ifs <;> simp [hw]

lemma tailw_le_one (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 ≤ w l) (h1 : ∑ l, w l = 1) (m : ℕ) :
    tailw w m ≤ 1 := by
  rw [← h1]; unfold tailw
  apply Finset.sum_le_sum; intro l _; split_ifs <;> simp [hw]

lemma tailw_nonneg (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 ≤ w l) (m : ℕ) : 0 ≤ tailw w m := by
  unfold tailw
  apply Finset.sum_nonneg; intro l _; split_ifs <;> simp [hw]

/-- Kuhn vertices are affinely independent. -/
lemma kv_affineIndependent (β : Fin n → V × V) (hβ : ∀ j, (β j).1 ≠ (β j).2)
    (σ : Equiv.Perm (Fin n)) : AffineIndependent ℝ (kv β σ) := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw0 hwv
  rw [Finset.weightedVSub_eq_linear_combination _ hw0] at hwv
  have htail : ∀ m : ℕ, m < n → tailw w m = 0 := by
    intro m hm
    have hj := congr_fun hwv (σ ⟨m, hm⟩)
    rw [sum_smul_kv, hw0, zero_smul, zero_add] at hj
    simp only [Equiv.symm_apply_apply, Pi.zero_apply] at hj
    rcases smul_eq_zero.1 hj with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm (hβ _)
  have htail' : ∀ m : ℕ, m ≤ n → tailw w m = 0 := by
    intro m hm
    rcases Nat.lt_or_ge m n with h | h
    · exact htail m h
    · exact tailw_ge w m h
  intro l
  rcases Nat.eq_zero_or_pos (l : ℕ) with h | h
  · have : l = 0 := Fin.ext h
    subst this
    have := tailw_zero_eq w
    rw [htail' 0 (Nat.zero_le _), hw0] at this
    linarith
  · have := tailw_eq w ((l : ℕ) - 1) (by omega)
    rw [htail' _ (by omega), htail' _ (by omega)] at this
    have hl : (⟨(l : ℕ) - 1 + 1, by omega⟩ : Fin (n+1)) = l := Fin.ext (by simp; omega)
    rw [hl] at this
    linarith

/-- threshold vertex -/
noncomputable def vth (β : Fin n → V × V) (u : Fin n → ℝ) (θ : ℝ) : Fin n → V :=
  fun j => if θ < u j then (β j).2 else (β j).1

lemma supp_sub (β : Fin n → V × V) (σ : Equiv.Perm (Fin n)) (w : Fin (n+1) → ℝ)
    (hw : ∀ l, 0 ≤ w l) (h1 : ∑ l, w l = 1) (l : Fin (n+1)) (hl : 0 < w l) :
    ∃ θ, 0 ≤ θ ∧ θ < 1 ∧ kv β σ l = vth β (fun j => tailw w (σ.symm j)) θ := by
  refine ⟨tailw w l, tailw_nonneg w hw _, ?_, ?_⟩
  · have : w l + tailw w l ≤ 1 := by
      rw [← h1]; unfold tailw
      have : w l = ∑ l' : Fin (n+1), if l' = l then w l' else 0 := by simp
      rw [this, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro l' _
      by_cases hh : l' = l
      · subst hh; simp
      · simp only [hh, if_false, zero_add]; split_ifs <;> simp [hw]
    linarith
  · funext j
    simp only [kv, vth]
    by_cases h : ((σ.symm j : Fin n) : ℕ) < (l : ℕ)
    · have := tailw_ge_add w hw _ l h
      simp only [h, if_true]
      rw [if_pos (by linarith)]
    · have := tailw_anti w hw (show (l : ℕ) ≤ (σ.symm j : ℕ) by omega)
      simp only [h, if_false]
      rw [if_neg (by linarith)]

lemma supp_sup (β : Fin n → V × V) (σ : Equiv.Perm (Fin n)) (w : Fin (n+1) → ℝ)
    (hw : ∀ l, 0 ≤ w l) (h1 : ∑ l, w l = 1) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ l, 0 < w l ∧ kv β σ l = vth β (fun j => tailw w (σ.symm j)) θ := by
  classical
  obtain ⟨l, hlS, hmin⟩ : ∃ l : Fin (n+1), tailw w l ≤ θ ∧
      ∀ l' : Fin (n+1), (l' : ℕ) < (l : ℕ) → θ < tailw w l' := by
    let S := Finset.univ.filter (fun l : Fin (n+1) => tailw w l ≤ θ)
    have hS : S.Nonempty := ⟨Fin.last n, by simp [S, tailw_ge w n le_rfl, hθ0]⟩
    refine ⟨S.min' hS, (Finset.mem_filter.1 (S.min'_mem hS)).2, ?_⟩
    intro l' hl'
    by_contra hc; push Not at hc
    have : S.min' hS ≤ l' := S.min'_le l' (by simp [S, hc])
    exact absurd hl' (not_lt.2 this)
  refine ⟨l, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (l : ℕ) with h | h
    · have hl0 : l = 0 := Fin.ext h
      subst hl0
      have := tailw_zero_eq w
      rw [h1] at this
      simp only [Fin.val_zero] at hlS
      linarith
    · have := tailw_eq w ((l : ℕ) - 1) (by omega)
      have hl' : (⟨(l : ℕ) - 1 + 1, by omega⟩ : Fin (n+1)) = l := Fin.ext (by simp only; omega)
      rw [hl', show (l : ℕ) - 1 + 1 = l by omega] at this
      have h2 := hmin ⟨(l : ℕ) - 1, by omega⟩ (by simp only; omega)
      simp only at h2
      linarith
  · funext j
    simp only [kv, vth]
    by_cases h : ((σ.symm j : Fin n) : ℕ) < (l : ℕ)
    · have := hmin ⟨(σ.symm j : ℕ), by have := (σ.symm j).2; omega⟩ h
      simp only [h, if_true]; rw [if_pos this]
    · have := tailw_anti w hw (show (l : ℕ) ≤ (σ.symm j : ℕ) by omega)
      simp only [h, if_false]; rw [if_neg (by linarith)]

lemma kv_injective (β : Fin n → V × V) (hβ : ∀ j, (β j).1 ≠ (β j).2) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (kv β σ) := (kv_affineIndependent β hβ σ).injective

lemma coord_eq (β : Fin n → V × V) (σ : Equiv.Perm (Fin n)) (w : Fin (n+1) → ℝ)
    (h1 : ∑ l, w l = 1) (j : Fin n) :
    (∑ l, w l • kv β σ l) j = (β j).1 + tailw w (σ.symm j) • ((β j).2 - (β j).1) := by
  rw [sum_smul_kv, h1, one_smul]

lemma param_inj {a b : V} (hab : a ≠ b) {u u' : ℝ} (h : a + u • (b - a) = a + u' • (b - a)) :
    u = u' := by
  have : (u - u') • (b - a) = 0 := by rw [sub_smul]; exact sub_eq_zero.2 (add_left_cancel h)
  rcases smul_eq_zero.1 this with h' | h'
  · linarith
  · exact absurd (sub_eq_zero.1 h').symm hab

lemma vth_eq_of_endpoint {a b : V} (hab : a ≠ b) {u θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hp : a + u • (b - a) = a ∨ a + u • (b - a) = b) :
    (if θ < u then b else a) = a + u • (b - a) := by
  rcases hp with h | h
  · have hu : u = 0 := param_inj hab (h.trans (by simp))
    subst hu; simp [not_lt.2 hθ0]
  · have hu : u = 1 := param_inj hab (h.trans (by simp))
    subst hu; simp [hθ1]

/-- supports of two convex representations of the same point coincide -/
lemma supp_eq (β β' : Fin n → V × V) (hβ : ∀ j, (β j).1 ≠ (β j).2) (hβ' : ∀ j, (β' j).1 ≠ (β' j).2)
    (σ σ' : Equiv.Perm (Fin n)) (w w' : Fin (n+1) → ℝ)
    (hw : ∀ l, 0 ≤ w l) (h1 : ∑ l, w l = 1) (hw' : ∀ l, 0 ≤ w' l) (h1' : ∑ l, w' l = 1)
    (hp : ∑ l, w l • kv β σ l = ∑ l, w' l • kv β' σ' l)
    (hcompat : ∀ j, β j = β' j ∨
      (((∑ l, w l • kv β σ l) j = (β j).1 ∨ (∑ l, w l • kv β σ l) j = (β j).2) ∧
       ((∑ l, w l • kv β σ l) j = (β' j).1 ∨ (∑ l, w l • kv β σ l) j = (β' j).2)))
    (q : Fin n → V) :
    (∃ l, 0 < w l ∧ kv β σ l = q) → (∃ l, 0 < w' l ∧ kv β' σ' l = q) := by
  rintro ⟨l, hl, rfl⟩
  obtain ⟨θ, hθ0, hθ1, hv⟩ := supp_sub β σ w hw h1 l hl
  obtain ⟨l', hl', hv'⟩ := supp_sup β' σ' w' hw' h1' θ hθ0 hθ1
  refine ⟨l', hl', ?_⟩
  rw [hv', hv]
  funext j
  simp only [vth]
  have e1 := coord_eq β σ w h1 j
  have e2 := coord_eq β' σ' w' h1' j
  rw [hp] at e1
  rcases hcompat j with hj | ⟨hj1, hj2⟩
  · rw [← hj] at e2 ⊢
    have := param_inj (hβ j) (e2.symm.trans e1)
    simp only [this]
  · rw [hp] at hj1 hj2
    rw [e1] at hj1; rw [e2] at hj2
    rw [vth_eq_of_endpoint (hβ j) hθ0 hθ1 hj1, vth_eq_of_endpoint (hβ' j) hθ0 hθ1 hj2, ← e1, ← e2]

end SPFGKuhn



namespace SPFGKuhn

open SPFacilityGraph

variable {k n : ℕ}

/-- all Kuhn faces (including empty) for boxes made of edges of `G` -/
def kfacesAll (G : MetricGraph k) (n : ℕ) : Set (Finset (Fin n → EuclideanSpace ℝ (Fin k))) :=
  {s | ∃ (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
      (σ : Equiv.Perm (Fin n)) (S : Finset (Fin (n+1))), (∀ j, β j ∈ G.edges) ∧ s = S.image (kv β σ)}

lemma edges_ne (G : MetricGraph k) (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
    (hβ : ∀ j, β j ∈ G.edges) : ∀ j, (β j).1 ≠ (β j).2 := fun j => G.fst_ne_snd _ (hβ j)

lemma coord_mem_segment (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
    (σ : Equiv.Perm (Fin n)) (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 ≤ w l) (h1 : ∑ l, w l = 1)
    (j : Fin n) : (∑ l, w l • kv β σ l) j ∈ segment ℝ (β j).1 (β j).2 := by
  rw [coord_eq β σ w h1 j, segment_eq_image']
  exact ⟨_, ⟨tailw_nonneg w hw _, tailw_le_one w hw h1 _⟩, rfl⟩

lemma kfacesAll_indep (G : MetricGraph k) (s : Finset (Fin n → EuclideanSpace ℝ (Fin k)))
    (hs : s ∈ kfacesAll G n) : AffineIndependent ℝ ((↑) : s → Fin n → EuclideanSpace ℝ (Fin k)) := by
  obtain ⟨β, σ, S, hβ, rfl⟩ := hs
  have h := (kv_affineIndependent β (edges_ne G β hβ) σ).range
  have hsub : ((S.image (kv β σ) : Finset _) : Set (Fin n → EuclideanSpace ℝ (Fin k))) ⊆
      Set.range (kv β σ) := by
    intro x hx
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨l, rfl⟩
  exact h.mono hsub

lemma kfacesAll_lower (G : MetricGraph k) : IsLowerSet (kfacesAll G n) := by
  classical
  rintro s t hts ⟨β, σ, S, hβ, rfl⟩
  refine ⟨β, σ, S.filter (fun l => kv β σ l ∈ t), hβ, ?_⟩
  ext x
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · intro hx
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 (hts hx)
    exact ⟨l, ⟨hl, hx⟩, rfl⟩
  · rintro ⟨l, ⟨-, hl⟩, rfl⟩; exact hl

lemma kfacesAll_inter (G : MetricGraph k) (s : Finset (Fin n → EuclideanSpace ℝ (Fin k)))
    (hs : s ∈ kfacesAll G n) (t : Finset (Fin n → EuclideanSpace ℝ (Fin k))) (ht : t ∈ kfacesAll G n) :
    convexHull ℝ (s : Set (Fin n → EuclideanSpace ℝ (Fin k))) ∩ convexHull ℝ ↑t ⊆
      convexHull ℝ (s ∩ t : Set (Fin n → EuclideanSpace ℝ (Fin k))) := by
  classical
  obtain ⟨β, σ, S, hβ, rfl⟩ := hs
  obtain ⟨β', σ', S', hβ', rfl⟩ := ht
  rintro p ⟨hp1, hp2⟩
  have hinj := kv_injective β (edges_ne G β hβ) σ
  have hinj' := kv_injective β' (edges_ne G β' hβ') σ'
  obtain ⟨w, hw0, hwS, hw1, rfl⟩ := (mem_convexHull_image_iff _ hinj S p).1 hp1
  obtain ⟨w', hw0', hwS', hw1', hp⟩ := (mem_convexHull_image_iff _ hinj' S' _).1 hp2
  have hcompat : ∀ j, β j = β' j ∨
      (((∑ l, w l • kv β σ l) j = (β j).1 ∨ (∑ l, w l • kv β σ l) j = (β j).2) ∧
       ((∑ l, w l • kv β σ l) j = (β' j).1 ∨ (∑ l, w l • kv β σ l) j = (β' j).2)) := by
    intro j
    by_cases hj : β j = β' j
    · exact Or.inl hj
    · right
      have m1 := coord_mem_segment β σ w hw0 hw1 j
      have m2 := coord_mem_segment β' σ' w' hw0' hw1' j
      rw [hp] at m2
      have := G.meet (β j) (hβ j) (β' j) (hβ' j) hj ⟨m1, m2⟩
      exact ⟨this.1, this.2⟩
  have hcompat' : ∀ j, β' j = β j ∨
      (((∑ l, w' l • kv β' σ' l) j = (β' j).1 ∨ (∑ l, w' l • kv β' σ' l) j = (β' j).2) ∧
       ((∑ l, w' l • kv β' σ' l) j = (β j).1 ∨ (∑ l, w' l • kv β' σ' l) j = (β j).2)) := by
    intro j
    rcases hcompat j with h | ⟨h1, h2⟩
    · exact Or.inl h.symm
    · right; rw [hp]; exact ⟨h2, h1⟩
  -- the positive support
  let P := (Finset.univ.filter (fun l => 0 < w l)).image (kv β σ)
  have hPs : (P : Set (Fin n → EuclideanSpace ℝ (Fin k))) ⊆ ↑(S.image (kv β σ)) ∩ ↑(S'.image (kv β' σ')) := by
    intro q hq
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hq
    have hl0 : 0 < w l := (Finset.mem_filter.1 hl).2
    refine ⟨Finset.mem_coe.2 (Finset.mem_image_of_mem _ ?_), ?_⟩
    · by_contra h; rw [hwS l h] at hl0; exact lt_irrefl _ hl0
    · obtain ⟨l', hl', he⟩ := supp_eq β β' (edges_ne G β hβ) (edges_ne G β' hβ') σ σ' w w' hw0 hw1
        hw0' hw1' hp.symm hcompat _ ⟨l, hl0, rfl⟩
      rw [← he]
      refine Finset.mem_coe.2 (Finset.mem_image_of_mem _ ?_)
      by_contra h; rw [hwS' l' h] at hl'; exact lt_irrefl _ hl'
  refine convexHull_mono (by simpa [Finset.coe_inter] using hPs) ?_
  rw [mem_convexHull_image_iff _ hinj]
  refine ⟨w, hw0, ?_, hw1, rfl⟩
  intro l hl
  by_contra h
  exact hl (Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_ne (hw0 l) (Ne.symm h)⟩)

/-- The Kuhn triangulation of `Gⁿ`. -/
def kuhnComplex (G : MetricGraph k) (n : ℕ) :
    Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k)) :=
  Geometry.SimplicialComplex.ofErase (kfacesAll G n) (kfacesAll_indep G) (kfacesAll_lower G)
    (fun s hs t ht => kfacesAll_inter G s hs t ht)

lemma mem_kuhn_faces (G : MetricGraph k) (s : Finset (Fin n → EuclideanSpace ℝ (Fin k))) :
    s ∈ (kuhnComplex G n).faces ↔ s ∈ kfacesAll G n ∧ s ≠ ∅ := by
  show s ∈ kfacesAll G n \ {∅} ↔ _
  simp

lemma kuhn_faces_finite (G : MetricGraph k) : (kuhnComplex G n).faces.Finite := by
  classical
  apply Set.Finite.subset (Set.finite_range (fun (t : (Fin n → G.edges) × Equiv.Perm (Fin n) ×
      Finset (Fin (n+1))) => t.2.2.image (kv (fun j => (t.1 j : EuclideanSpace ℝ (Fin k) ×
        EuclideanSpace ℝ (Fin k))) t.2.1)))
  intro s hs
  obtain ⟨⟨β, σ, S, hβ, rfl⟩, -⟩ := (mem_kuhn_faces G s).1 hs
  exact ⟨(fun j => ⟨β j, hβ j⟩, σ, S), rfl⟩

/-- the full Kuhn simplex is a face -/
lemma full_mem_faces (G : MetricGraph k) (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
    (hβ : ∀ j, β j ∈ G.edges) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.image (kv β σ) ∈ (kuhnComplex G n).faces := by
  rw [mem_kuhn_faces]
  refine ⟨⟨β, σ, _, hβ, rfl⟩, ?_⟩
  rw [← Finset.nonempty_iff_ne_empty]
  exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩

lemma facet_eq (G : MetricGraph k) (s : Finset (Fin n → EuclideanSpace ℝ (Fin k)))
    (hs : s ∈ (kuhnComplex G n).facets) :
    ∃ (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (σ : Equiv.Perm (Fin n)),
      (∀ j, β j ∈ G.edges) ∧ s = Finset.univ.image (kv β σ) := by
  obtain ⟨hsf, hmax⟩ := Geometry.SimplicialComplex.mem_facets.1 hs
  obtain ⟨⟨β, σ, S, hβ, rfl⟩, -⟩ := (mem_kuhn_faces G _).1 hsf
  refine ⟨β, σ, hβ, hmax _ (full_mem_faces G β hβ σ) ?_⟩
  exact Finset.image_subset_image (Finset.subset_univ S)

/-- every point of `Gⁿ` lies in a full Kuhn simplex -/
lemma exists_kuhn_rep (G : MetricGraph k) (p : Fin n → EuclideanSpace ℝ (Fin k))
    (hp : ∀ j, p j ∈ G.carrier) :
    ∃ (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (σ : Equiv.Perm (Fin n))
      (w : Fin (n+1) → ℝ), (∀ j, β j ∈ G.edges) ∧ (∀ l, 0 ≤ w l) ∧ ∑ l, w l = 1 ∧
      ∑ l, w l • kv β σ l = p := by
  classical
  have hex : ∀ j, ∃ e ∈ G.edges, ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ p j = e.1 + u • (e.2 - e.1) := by
    intro j
    obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.1 (hp j)
    rw [segment_eq_image'] at hpe
    obtain ⟨u, ⟨hu0, hu1⟩, hu⟩ := hpe
    exact ⟨e, he, u, hu0, hu1, hu.symm⟩
  choose β hβ u hu0 hu1 hpu using hex
  let σ := Tuple.sort (fun j => -u j)
  have hanti : ∀ a b : Fin n, a ≤ b → u (σ b) ≤ u (σ a) := by
    intro a b hab
    have := Tuple.monotone_sort (fun j => -u j) hab
    simp only [Function.comp] at this
    linarith
  let U : ℕ → ℝ := fun m => if h : m < n then u (σ ⟨m, h⟩) else 0
  have hUanti : ∀ m, U (m + 1) ≤ U m := by
    intro m
    simp only [U]
    by_cases h1 : m + 1 < n
    · rw [dif_pos h1, dif_pos (by omega)]
      exact hanti ⟨m, by omega⟩ ⟨m+1, h1⟩ (by simp [Fin.le_def])
    · rw [dif_neg h1]
      split_ifs with h2
      · exact hu0 _
      · exact le_rfl
  have hU1 : ∀ m, U m ≤ 1 := by
    intro m; simp only [U]; split_ifs
    · exact hu1 _
    · exact zero_le_one
  let w : Fin (n+1) → ℝ := fun l => (if (l : ℕ) = 0 then 1 else U ((l : ℕ) - 1)) - U l
  have htail : ∀ m, m ≤ n → tailw w m = U m := by
    intro m hm
    induction h : n - m generalizing m with
    | zero =>
      have : m = n := by omega
      subst this
      rw [tailw_ge w _ le_rfl]; simp [U]
    | succ d ih =>
      rw [tailw_eq w m (by omega), ih (m + 1) (by omega) (by omega)]
      simp only [w, show m + 1 ≠ 0 by omega, if_false, show m + 1 - 1 = m by omega]
      ring
  refine ⟨β, σ, w, hβ, ?_, ?_, ?_⟩
  · intro l
    simp only [w]
    split_ifs with h
    · rw [h]; linarith [hU1 0]
    · have := hUanti ((l : ℕ) - 1)
      rw [show (l : ℕ) - 1 + 1 = l by omega] at this
      linarith
  · have := tailw_zero_eq w
    rw [htail 0 (Nat.zero_le _)] at this
    have hw0 : w 0 = 1 - U 0 := by simp [w]
    linarith
  · funext j
    have h1 : ∑ l, w l = 1 := by
      have := tailw_zero_eq w
      rw [htail 0 (Nat.zero_le _)] at this
      have hw0 : w 0 = 1 - U 0 := by simp [w]
      linarith
    rw [coord_eq β σ w h1 j, htail _ (by have := (σ.symm j).2; omega), hpu j]
    simp only [U, dif_pos (σ.symm j).2]
    simp

lemma kuhn_space (G : MetricGraph k) :
    (kuhnComplex G n).space = Set.range (G.embed (n := n)) := by
  classical
  ext p
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s, hs, hps⟩
    obtain ⟨⟨β, σ, S, hβ, rfl⟩, -⟩ := (mem_kuhn_faces G s).1 hs
    obtain ⟨w, hw0, -, hw1, rfl⟩ :=
      (mem_convexHull_image_iff _ (kv_injective β (edges_ne G β hβ) σ) S _).1 hps
    refine ⟨fun j => ⟨_, Set.mem_biUnion (hβ j) (coord_mem_segment β σ w hw0 hw1 j)⟩, ?_⟩
    funext j; rfl
  · rintro ⟨x, rfl⟩
    obtain ⟨β, σ, w, hβ, hw0, hw1, hp⟩ := exists_kuhn_rep G (G.embed x) (fun j => (x j).2)
    refine ⟨_, full_mem_faces G β hβ σ, ?_⟩
    rw [mem_convexHull_image_iff _ (kv_injective β (edges_ne G β hβ) σ)]
    exact ⟨w, hw0, fun l hl => absurd (Finset.mem_univ l) hl, hw1, hp⟩

lemma tailw_lt_one (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 < w l) (h1 : ∑ l, w l = 1) (m : ℕ) :
    tailw w m < 1 := by
  have h0 := tailw_anti w (fun l => (hw l).le) (Nat.zero_le m)
  have := tailw_zero_eq w
  have := hw 0
  linarith

lemma tailw_pos (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 < w l) (m : ℕ) (hm : m < n) :
    0 < tailw w m := by
  have := tailw_ge_add w (fun l => (hw l).le) m ⟨m + 1, by omega⟩ (by simp)
  have := tailw_nonneg w (fun l => (hw l).le) (m + 1)
  have := hw ⟨m + 1, by omega⟩
  simp only at *
  linarith

lemma tailw_strict (w : Fin (n+1) → ℝ) (hw : ∀ l, 0 < w l) (m m' : ℕ) (hmm : m < m')
    (hm' : m' < n + 1) : tailw w m' < tailw w m := by
  have := tailw_ge_add w (fun l => (hw l).le) m ⟨m', hm'⟩ hmm
  have := hw ⟨m', hm'⟩
  simp only at *
  linarith

lemma facet_generic (G : MetricGraph k) (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
    (hβ : ∀ j, β j ∈ G.edges) (σ : Equiv.Perm (Fin n)) :
    ∃ R : Set (Fin n → EuclideanSpace ℝ (Fin k)),
      R ⊆ convexHull ℝ ((Finset.univ.image (kv β σ) : Finset _) : Set (Fin n → EuclideanSpace ℝ (Fin k))) ∧
      Convex ℝ R ∧
      convexHull ℝ ((Finset.univ.image (kv β σ) : Finset _) : Set (Fin n → EuclideanSpace ℝ (Fin k))) ⊆
        closure R ∧
      ∀ p ∈ R, (∀ i j, i ≠ j → p i ≠ p j) ∧ ∀ i, ∀ e ∈ G.edges, p i ≠ e.1 ∧ p i ≠ e.2 := by
  classical
  have hinj := kv_injective β (edges_ne G β hβ) σ
  let R : Set (Fin n → EuclideanSpace ℝ (Fin k)) :=
    {p | ∃ w : Fin (n+1) → ℝ, (∀ l, 0 < w l) ∧ ∑ l, w l = 1 ∧ ∑ l, w l • kv β σ l = p}
  have hRsub : R ⊆ convexHull ℝ ((Finset.univ.image (kv β σ) : Finset _) : Set _) := by
    rintro p ⟨w, hw, hw1, rfl⟩
    rw [mem_convexHull_image_iff _ hinj]
    exact ⟨w, fun l => (hw l).le, fun l hl => absurd (Finset.mem_univ l) hl, hw1, rfl⟩
  refine ⟨R, hRsub, ?_, ?_, ?_⟩
  · rintro p ⟨w, hw, hw1, rfl⟩ q ⟨w', hw', hw1', rfl⟩ a b ha hb hab
    refine ⟨fun l => a * w l + b * w' l, ?_, ?_, ?_⟩
    · intro l
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hw l)) (mul_nonneg hb (hw' l).le)
      · subst ha'; simp at hab; subst hab; simp [hw' l]
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, hw1']; linarith
    · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro l _
      rw [add_smul, mul_smul, mul_smul]
  · intro p hp
    rw [mem_convexHull_image_iff _ hinj] at hp
    obtain ⟨w, hw0, -, hw1, rfl⟩ := hp
    let c : Fin n → EuclideanSpace ℝ (Fin k) := ∑ l, (1 / (n + 1 : ℝ)) • kv β σ l
    have hc1 : ∑ _l : Fin (n+1), (1 / (n + 1 : ℝ)) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; field_simp
    have hopen : openSegment ℝ c (∑ l, w l • kv β σ l) ⊆ R := by
      rintro q ⟨a, b, ha, hb, hab, rfl⟩
      refine ⟨fun l => a * (1 / (n + 1 : ℝ)) + b * w l, ?_, ?_, ?_⟩
      · intro l; exact add_pos_of_pos_of_nonneg (mul_pos ha (by positivity)) (mul_nonneg hb.le (hw0 l))
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hc1, hw1]; linarith
      · simp only [c]
        rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro l _
        rw [add_smul, mul_smul, mul_smul]
    exact closure_mono hopen (segment_subset_closure_openSegment (right_mem_segment ℝ _ _))
  · rintro p ⟨w, hw, hw1, rfl⟩
    have hcoord := coord_eq β σ w hw1
    have hu : ∀ j, 0 < tailw w (σ.symm j) ∧ tailw w (σ.symm j) < 1 := fun j =>
      ⟨tailw_pos w hw _ (σ.symm j).2, tailw_lt_one w hw hw1 _⟩
    have hnotend : ∀ j, ∀ e ∈ G.edges, (∑ l, w l • kv β σ l) j ≠ e.1 ∧
        (∑ l, w l • kv β σ l) j ≠ e.2 := by
      intro j e he
      have hmem : (∑ l, w l • kv β σ l) j ∈ segment ℝ (β j).1 (β j).2 :=
        coord_mem_segment β σ w (fun l => (hw l).le) hw1 j
      have key : ¬ ((∑ l, w l • kv β σ l) j = (β j).1 ∨ (∑ l, w l • kv β σ l) j = (β j).2) := by
        rintro (h | h)
        · rw [hcoord] at h
          have : tailw w (σ.symm j) = 0 := param_inj (edges_ne G β hβ j) (h.trans (by simp))
          linarith [(hu j).1]
        · rw [hcoord] at h
          have : tailw w (σ.symm j) = 1 := param_inj (edges_ne G β hβ j) (h.trans (by simp))
          linarith [(hu j).2]
      by_cases hej : e = β j
      · subst hej; exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩
      · constructor
        · intro h
          have hm2 : (∑ l, w l • kv β σ l) j ∈ segment ℝ e.1 e.2 := by rw [h]; exact left_mem_segment ℝ _ _
          exact key (G.meet _ (hβ j) e he (Ne.symm hej) ⟨hmem, hm2⟩).1
        · intro h
          have hm2 : (∑ l, w l • kv β σ l) j ∈ segment ℝ e.1 e.2 := by rw [h]; exact right_mem_segment ℝ _ _
          exact key (G.meet _ (hβ j) e he (Ne.symm hej) ⟨hmem, hm2⟩).1
    refine ⟨?_, hnotend⟩
    intro i j hij heq
    by_cases hb : β i = β j
    · have e1 := hcoord i
      have e2 := hcoord j
      rw [heq, e2, hb] at e1
      have := param_inj (edges_ne G β hβ j) e1
      have hne : ((σ.symm i : Fin n) : ℕ) ≠ ((σ.symm j : Fin n) : ℕ) := by
        intro h; exact hij (σ.symm.injective (Fin.ext h))
      rcases lt_or_gt_of_ne hne with h | h
      · have := tailw_strict w hw _ _ h (by have := (σ.symm j).2; omega); linarith
      · have := tailw_strict w hw _ _ h (by have := (σ.symm i).2; omega); linarith
    · have hmi := coord_mem_segment β σ w (fun l => (hw l).le) hw1 i
      have hmj := coord_mem_segment β σ w (fun l => (hw l).le) hw1 j
      rw [heq] at hmi
      have := G.meet _ (hβ j) _ (hβ i) (Ne.symm hb) ⟨hmj, hmi⟩
      rcases this.1 with h | h
      · exact (hnotend j (β j) (hβ j)).1 h
      · exact (hnotend j (β j) (hβ j)).2 h

end SPFGKuhn



namespace SPFGKuhn

open SPFacilityGraph

variable {k : ℕ}

/-- parametrization of a segment -/
def par (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (t : ℝ) : EuclideanSpace ℝ (Fin k) :=
  e.1 + t • (e.2 - e.1)

lemma par_inj {e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)} (he : e.1 ≠ e.2) :
    Function.Injective (par e) := fun _ _ h => param_inj he h

/-- breakpoint parameters of an edge -/
noncomputable def bparams (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) : Finset ℝ :=
  insert 0 (insert 1 (((B.finite_toSet.preimage (par_inj he).injOn).toFinset).filter
    (fun t => t ∈ Set.Icc (0:ℝ) 1)))

lemma bparams_Icc (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    ∀ t ∈ bparams B e he, t ∈ Set.Icc (0:ℝ) 1 := by
  intro t ht
  simp only [bparams, Finset.mem_insert, Finset.mem_filter] at ht
  rcases ht with rfl | rfl | ⟨-, h⟩
  · exact ⟨le_rfl, zero_le_one⟩
  · exact ⟨zero_le_one, le_rfl⟩
  · exact h

lemma bparams_card (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    2 ≤ (bparams B e he).card := by
  have : ({0, 1} : Finset ℝ) ⊆ bparams B e he := by
    intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> simp [bparams]
  have h2 : ({0, 1} : Finset ℝ).card = 2 := by simp
  rw [← h2]; exact Finset.card_le_card this

/-- sorted breakpoint parameters -/
noncomputable def sp (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    Fin ((bparams B e he).card - 1 + 1) ↪o ℝ :=
  (bparams B e he).orderEmbOfFin (by have := bparams_card B e he; omega)

lemma sp_zero (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    sp B e he 0 = 0 := by
  have := Finset.orderEmbOfFin_zero (s := bparams B e he)
    (by have := bparams_card B e he; omega : (bparams B e he).card = (bparams B e he).card - 1 + 1)
    (Nat.succ_pos _)
  refine this.trans (le_antisymm (Finset.min'_le _ _ (by simp [bparams])) ?_)
  exact (bparams_Icc B e he _ (Finset.min'_mem _ _)).1

lemma sp_last (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    sp B e he (Fin.last _) = 1 := by
  have := Finset.orderEmbOfFin_last (s := bparams B e he)
    (by have := bparams_card B e he; omega : (bparams B e he).card = (bparams B e he).card - 1 + 1)
    (Nat.succ_pos _)
  refine (show sp B e he (Fin.last _) = _ from by
    simp only [sp]; congr 1).trans (this.trans (le_antisymm ?_ (Finset.le_max' _ _ (by simp [bparams]))))
  exact (bparams_Icc B e he _ (Finset.max'_mem _ _)).2

lemma sp_Icc (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) (i) :
    sp B e he i ∈ Set.Icc (0:ℝ) 1 :=
  bparams_Icc B e he _ (Finset.orderEmbOfFin_mem _ _ _)

/-- subedges of an edge -/
noncomputable def subedges (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    Finset (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
  Finset.univ.image (fun i : Fin ((bparams B e he).card - 1) =>
    (par e (sp B e he i.castSucc), par e (sp B e he i.succ)))

lemma par_mem_segment (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) : par e t ∈ segment ℝ e.1 e.2 := by
  rw [segment_eq_image']; exact ⟨t, ht, rfl⟩

lemma mem_segment_iff_par (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (q) :
    q ∈ segment ℝ e.1 e.2 ↔ ∃ t ∈ Set.Icc (0:ℝ) 1, q = par e t := by
  rw [segment_eq_image']
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

/-- points of the segment between two parameter values -/
lemma mem_segment_par (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) {t1 t2 : ℝ}
    (h12 : t1 ≤ t2) (q) : q ∈ segment ℝ (par e t1) (par e t2) ↔ ∃ t ∈ Set.Icc t1 t2, q = par e t := by
  have : segment ℝ (par e t1) (par e t2) = par e '' segment ℝ t1 t2 := by
    have hpar : par e = (AffineMap.lineMap e.1 e.2 : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin k)) := by
      funext t; simp [par, AffineMap.lineMap_apply, add_comm]
    rw [hpar, ← image_segment]
  rw [this, segment_eq_Icc h12]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

lemma sp_strictMono (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    StrictMono (sp B e he) := (sp B e he).strictMono

lemma mem_subedges (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) (e') :
    e' ∈ subedges B e he ↔ ∃ i : Fin ((bparams B e he).card - 1),
      e' = (par e (sp B e he i.castSucc), par e (sp B e he i.succ)) := by
  simp only [subedges, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

lemma subedge_seg_sub (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) (e')
    (h : e' ∈ subedges B e he) : segment ℝ e'.1 e'.2 ⊆ segment ℝ e.1 e.2 := by
  obtain ⟨i, rfl⟩ := (mem_subedges B e he e').1 h
  exact (convex_segment _ _).segment_subset (par_mem_segment e (sp_Icc B e he _))
    (par_mem_segment e (sp_Icc B e he _))

lemma union_subedges (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2) :
    ⋃ e' ∈ subedges B e he, segment ℝ e'.1 e'.2 = segment ℝ e.1 e.2 := by
  apply le_antisymm
  · exact Set.iUnion₂_subset (fun e' h => subedge_seg_sub B e he e' h)
  · intro q hq
    obtain ⟨t, ht, rfl⟩ := (mem_segment_iff_par e q).1 hq
    -- find the subinterval containing t
    classical
    set m := (bparams B e he).card - 1
    have hm : 1 ≤ m := by have := bparams_card B e he; omega
    let S := Finset.univ.filter (fun l : Fin (m + 1) => t ≤ sp B e he l)
    have hS : S.Nonempty := ⟨Fin.last m, by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      have := sp_last B e he; rw [this]; exact ht.2⟩
    set l := S.min' hS with hl
    have hlS : t ≤ sp B e he l := (Finset.mem_filter.1 (S.min'_mem hS)).2
    by_cases hl0 : (l : ℕ) = 0
    · -- t = 0
      have : l = 0 := Fin.ext hl0
      rw [this, sp_zero] at hlS
      have ht0 : t = 0 := le_antisymm hlS ht.1
      refine Set.mem_biUnion (x := (par e (sp B e he (⟨0, by omega⟩ : Fin m).castSucc),
        par e (sp B e he (⟨0, by omega⟩ : Fin m).succ))) ((mem_subedges B e he _).2 ⟨_, rfl⟩) ?_
      have : (⟨0, by omega⟩ : Fin m).castSucc = 0 := rfl
      rw [this, sp_zero, ← ht0]; exact left_mem_segment ℝ _ _
    · let i : Fin m := ⟨(l : ℕ) - 1, by have := l.2; omega⟩
      have hi1 : i.succ = l := Fin.ext (by simp [i]; omega)
      have hi2 : sp B e he i.castSucc < t := by
        by_contra hc; push Not at hc
        have : l ≤ i.castSucc := S.min'_le _ (by simp [S, hc])
        rw [← hi1] at this
        exact absurd this (not_le.2 Fin.castSucc_lt_succ)
      refine Set.mem_biUnion ((mem_subedges B e he _).2 ⟨i, rfl⟩) ?_
      simp only
      rw [mem_segment_par e ((sp_strictMono B e he).monotone (Fin.castSucc_le_succ i))]
      exact ⟨t, ⟨hi2.le, by rw [hi1]; exact hlS⟩, rfl⟩

lemma subedge_param (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2)
    (i : Fin ((bparams B e he).card - 1)) (q)
    (hq : q ∈ segment ℝ (par e (sp B e he i.castSucc)) (par e (sp B e he i.succ))) :
    ∃ t ∈ Set.Icc (sp B e he i.castSucc) (sp B e he i.succ), q = par e t :=
  (mem_segment_par e ((sp_strictMono B e he).monotone (Fin.castSucc_le_succ i)) q).1 hq

lemma subedge_endpoint (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2)
    (i : Fin ((bparams B e he).card - 1)) (q)
    (hq : q ∈ segment ℝ (par e (sp B e he i.castSucc)) (par e (sp B e he i.succ)))
    (hend : q = e.1 ∨ q = e.2) :
    q = par e (sp B e he i.castSucc) ∨ q = par e (sp B e he i.succ) := by
  obtain ⟨t, ht, rfl⟩ := subedge_param B e he i q hq
  have h0 := sp_Icc B e he i.castSucc
  have h1 := sp_Icc B e he i.succ
  rcases hend with h | h
  · have : t = 0 := par_inj he (h.trans (by simp [par]))
    subst this
    left; congr 1; linarith [ht.1, h0.1]
  · have : t = 1 := par_inj he (h.trans (by simp [par]))
    subst this
    right; congr 1; linarith [ht.2, h1.2]

lemma subedge_same (B : Finset (EuclideanSpace ℝ (Fin k)))
    (e : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) (he : e.1 ≠ e.2)
    (i j : Fin ((bparams B e he).card - 1)) (hij : i ≠ j) (q)
    (hqi : q ∈ segment ℝ (par e (sp B e he i.castSucc)) (par e (sp B e he i.succ)))
    (hqj : q ∈ segment ℝ (par e (sp B e he j.castSucc)) (par e (sp B e he j.succ))) :
    (q = par e (sp B e he i.castSucc) ∨ q = par e (sp B e he i.succ)) ∧
    (q = par e (sp B e he j.castSucc) ∨ q = par e (sp B e he j.succ)) := by
  obtain ⟨t, ht, rfl⟩ := subedge_param B e he i q hqi
  obtain ⟨t', ht', htt⟩ := subedge_param B e he j _ hqj
  have := par_inj he htt
  subst this
  have hsm := sp_strictMono B e he
  rcases lt_or_gt_of_ne hij with h | h
  · -- i < j : then i.succ ≤ j.castSucc
    have hle : i.succ ≤ j.castSucc := by rw [Fin.le_def]; simp; rw [Fin.lt_def] at h; omega
    have h1 := hsm.monotone hle
    have : t = sp B e he i.succ := le_antisymm ht.2 (h1.trans ht'.1)
    have : t = sp B e he j.castSucc := le_antisymm (ht.2.trans h1) ht'.1
    exact ⟨Or.inr (by congr 1), Or.inl (by congr 1)⟩
  · have hle : j.succ ≤ i.castSucc := by rw [Fin.le_def]; simp; rw [Fin.lt_def] at h; omega
    have h1 := hsm.monotone hle
    have : t = sp B e he i.castSucc := le_antisymm (ht'.2.trans h1) ht.1
    have : t = sp B e he j.succ := le_antisymm ht'.2 (h1.trans ht.1)
    exact ⟨Or.inl (by congr 1), Or.inr (by congr 1)⟩

/-- The refinement of `G` at the points of `B`. -/
noncomputable def refineG (G : MetricGraph k) (B : Finset (EuclideanSpace ℝ (Fin k))) : MetricGraph k where
  edges := G.edges.attach.biUnion (fun e => subedges B e.1 (G.fst_ne_snd e.1 e.2))
  edges_nonempty := by
    obtain ⟨e, he⟩ := G.edges_nonempty
    have hm : 0 < (bparams B e (G.fst_ne_snd e he)).card - 1 := by
      have := bparams_card B e (G.fst_ne_snd e he); omega
    exact ⟨_, Finset.mem_biUnion.2 ⟨⟨e, he⟩, Finset.mem_attach _ _,
      (mem_subedges B e _ _).2 ⟨⟨0, hm⟩, rfl⟩⟩⟩
  fst_ne_snd := by
    intro e' he'
    obtain ⟨e, -, he'⟩ := Finset.mem_biUnion.1 he'
    obtain ⟨i, rfl⟩ := (mem_subedges B _ _ _).1 he'
    intro h
    have := par_inj (G.fst_ne_snd e.1 e.2) h
    exact absurd this (ne_of_lt ((sp_strictMono B _ _) Fin.castSucc_lt_succ))
  meet := by
    intro e1' he1' e2' he2' hne q ⟨hq1, hq2⟩
    obtain ⟨e1, -, he1'⟩ := Finset.mem_biUnion.1 he1'
    obtain ⟨e2, -, he2'⟩ := Finset.mem_biUnion.1 he2'
    obtain ⟨i, rfl⟩ := (mem_subedges B _ _ _).1 he1'
    obtain ⟨j, rfl⟩ := (mem_subedges B _ _ _).1 he2'
    by_cases h12 : e1 = e2
    · subst h12
      have hij : i ≠ j := by rintro rfl; exact hne rfl
      exact subedge_same B _ _ i j hij q hq1 hq2
    · have hs1 := subedge_seg_sub B _ _ _ he1' hq1
      have hs2 := subedge_seg_sub B _ _ _ he2' hq2
      have hne' : e1.1 ≠ e2.1 := fun h => h12 (Subtype.ext h)
      have := G.meet e1.1 e1.2 e2.1 e2.2 hne' ⟨hs1, hs2⟩
      exact ⟨subedge_endpoint B _ _ i q hq1 this.1, subedge_endpoint B _ _ j q hq2 this.2⟩
  connected := by
    have : (⋃ e' ∈ G.edges.attach.biUnion (fun e => subedges B e.1 (G.fst_ne_snd e.1 e.2)),
        segment ℝ e'.1 e'.2) = ⋃ e ∈ G.edges, segment ℝ e.1 e.2 := by
      ext q
      simp only [Set.mem_iUnion, Finset.mem_biUnion, Finset.mem_attach, true_and, exists_prop]
      constructor
      · rintro ⟨e', ⟨e, he'⟩, hq⟩
        exact ⟨e.1, e.2, subedge_seg_sub B _ _ _ he' hq⟩
      · rintro ⟨e, he, hq⟩
        rw [← union_subedges B e (G.fst_ne_snd e he)] at hq
        obtain ⟨e', he', hq'⟩ := Set.mem_iUnion₂.1 hq
        exact ⟨e', ⟨⟨e, he⟩, he'⟩, hq'⟩
    rw [this]; exact G.connected

lemma refineG_carrier (G : MetricGraph k) (B : Finset (EuclideanSpace ℝ (Fin k))) :
    (refineG G B).carrier = G.carrier := by
  ext q
  simp only [MetricGraph.carrier, refineG, Set.mem_iUnion, Finset.mem_biUnion, Finset.mem_attach,
    true_and, exists_prop]
  constructor
  · rintro ⟨e', ⟨e, he'⟩, hq⟩
    exact ⟨e.1, e.2, subedge_seg_sub B _ _ _ he' hq⟩
  · rintro ⟨e, he, hq⟩
    rw [← union_subedges B e (G.fst_ne_snd e he)] at hq
    obtain ⟨e', he', hq'⟩ := Set.mem_iUnion₂.1 hq
    exact ⟨e', ⟨⟨e, he⟩, he'⟩, hq'⟩

lemma refineG_edge_sub (G : MetricGraph k) (B : Finset (EuclideanSpace ℝ (Fin k))) (e')
    (he' : e' ∈ (refineG G B).edges) :
    ∃ e ∈ G.edges, segment ℝ e'.1 e'.2 ⊆ segment ℝ e.1 e.2 := by
  obtain ⟨e, -, he'⟩ := Finset.mem_biUnion.1 he'
  exact ⟨e.1, e.2, subedge_seg_sub B _ _ _ he'⟩

lemma refineG_vertex (G : MetricGraph k) (B : Finset (EuclideanSpace ℝ (Fin k))) (b)
    (hb : b ∈ B) (hbc : b ∈ G.carrier) :
    ∃ e' ∈ (refineG G B).edges, b = e'.1 ∨ b = e'.2 := by
  obtain ⟨e, he, hbe⟩ := Set.mem_iUnion₂.1 hbc
  obtain ⟨t, ht, rfl⟩ := (mem_segment_iff_par e b).1 hbe
  have hne := G.fst_ne_snd e he
  have htB : t ∈ bparams B e hne := by
    simp only [bparams, Finset.mem_insert, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_preimage, Finset.mem_coe]
    right; right; exact ⟨hb, ht⟩
  have : t ∈ Set.range (sp B e hne) := by
    simp only [sp, Finset.range_orderEmbOfFin]; exact htB
  obtain ⟨l, rfl⟩ := this
  have hm : 1 ≤ (bparams B e hne).card - 1 := by have := bparams_card B e hne; omega
  by_cases hl : (l : ℕ) < (bparams B e hne).card - 1
  · let i : Fin ((bparams B e hne).card - 1) := ⟨l, hl⟩
    refine ⟨_, Finset.mem_biUnion.2 ⟨⟨e, he⟩, Finset.mem_attach _ _, (mem_subedges B e _ _).2 ⟨i, rfl⟩⟩, ?_⟩
    left; congr 2
  · let i : Fin ((bparams B e hne).card - 1) := ⟨(l : ℕ) - 1, by omega⟩
    refine ⟨_, Finset.mem_biUnion.2 ⟨⟨e, he⟩, Finset.mem_attach _ _, (mem_subedges B e _ _).2 ⟨i, rfl⟩⟩, ?_⟩
    right; congr 2; ext; simp [i]; have := l.2; omega

end SPFGKuhn



namespace SPFGKuhn

open SPFacilityGraph

variable {k n : ℕ}

lemma norm_le_dist (G : MetricGraph k) (a b : G.Pt) :
    ‖(a : EuclideanSpace ℝ (Fin k)) - b‖ ≤ G.dist a b := by
  obtain ⟨m, p, h0, hm, -, hL⟩ := G.exists_walk_eq_dist a b
  rw [← hL]
  have h := Finset.sum_range_sub p m
  rw [hm, h0] at h
  rw [norm_sub_rev, ← h]
  exact norm_sum_le _ _

lemma dist_le_norm_of_seg (G : MetricGraph k) (a b : G.Pt) (e) (he : e ∈ G.edges)
    (ha : (a : EuclideanSpace ℝ (Fin k)) ∈ segment ℝ e.1 e.2)
    (hb : (b : EuclideanSpace ℝ (Fin k)) ∈ segment ℝ e.1 e.2) :
    G.dist a b ≤ ‖(a : EuclideanSpace ℝ (Fin k)) - b‖ := by
  have := G.dist_le_walk a b 1 (fun j => if j = 0 then (a : EuclideanSpace ℝ (Fin k)) else b)
    (by simp) (by simp) (by
      intro j hj
      have : j = 0 := by omega
      subst this
      exact ⟨e, he, by simpa using ha, by simpa using hb⟩)
  simpa [norm_sub_rev] using this

lemma eq_of_dist_zero (G : MetricGraph k) (a b : G.Pt) (h : G.dist a b = 0) : a = b := by
  have := norm_le_dist G a b
  rw [h] at this
  exact Subtype.ext (sub_eq_zero.1 (norm_le_zero_iff.1 this))

lemma dist_nonneg' (G : MetricGraph k) (a b : G.Pt) : 0 ≤ G.dist a b :=
  (norm_nonneg _).trans (norm_le_dist G a b)

/-- coordinatewise Lipschitz implies Lipschitz for the sum of coordinate distances -/
lemma lip_chain (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hLip : ∀ (x : Profile G n) (i : Fin n) (y : G.Pt),
      G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i))
    (x x' : Profile G n) : G.dist (M x) (M x') ≤ ∑ j, G.dist (x j) (x' j) := by
  classical
  have key : ∀ S : Finset (Fin n),
      G.dist (M x) (M (fun j => if j ∈ S then x' j else x j)) ≤ ∑ j ∈ S, G.dist (x j) (x' j) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.sum_empty]
      have : (fun j => x j) = x := rfl
      rw [this]
      exact le_of_eq (by
        have h := G.dist_triangle (M x) (M x) (M x)
        have h2 := dist_nonneg' G (M x) (M x)
        have h3 : G.dist (M x) (M x) ≤ 0 := by
          have := G.dist_le_walk (M x) (M x) 0 (fun _ => (M x : EuclideanSpace ℝ (Fin k))) rfl rfl
            (fun j hj => absurd hj (by omega))
          simpa using this
        linarith)
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      have hz : (fun j => if j ∈ insert a S then x' j else x j) =
          Function.update (fun j => if j ∈ S then x' j else x j) a (x' a) := by
        funext j
        by_cases hj : j = a
        · subst hj; simp
        · simp [Function.update_of_ne hj, Finset.mem_insert, hj]
      rw [hz]
      have h1 := hLip (fun j => if j ∈ S then x' j else x j) a (x' a)
      simp only [ha, if_false] at h1
      have h2 := G.dist_triangle (M x) (M (fun j => if j ∈ S then x' j else x j))
        (M (Function.update (fun j => if j ∈ S then x' j else x j) a (x' a)))
      rw [G.dist_comm (M (fun j => if j ∈ S then x' j else x j)), G.dist_comm (x' a)] at *
      linarith
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  exact this

lemma range_embed_eq (G1 G2 : MetricGraph k) (h : G1.carrier = G2.carrier) :
    Set.range (G1.embed (n := n)) = Set.range (G2.embed (n := n)) := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨fun j => ⟨x j, h ▸ (x j).2⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨fun j => ⟨x j, h.symm ▸ (x j).2⟩, rfl⟩

/-- The main facet lemma: on each Kuhn facet the mechanism is one selector. -/
lemma facet_selector (G : MetricGraph k) (M : Profile G n → G.Pt) (W : Finset G.Pt)
    (hLip : ∀ (x : Profile G n) (i : Fin n) (y : G.Pt),
      G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i))
    (hval : ∀ x, (∃ i, M x = x i) ∨ M x ∈ W)
    (β : Fin n → EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k))
    (hβ : ∀ j, β j ∈ (refineG G (W.image Subtype.val)).edges) (σ : Equiv.Perm (Fin n)) :
    ∃ f : Selector G n W, ∀ x : Profile G n,
      G.embed x ∈ convexHull ℝ ((Finset.univ.image (kv β σ) : Finset _) :
        Set (Fin n → EuclideanSpace ℝ (Fin k))) → M x = f.eval x := by
  classical
  set B : Finset (EuclideanSpace ℝ (Fin k)) := W.image Subtype.val with hB
  set G' := refineG G B with hG'
  have hinj := kv_injective β (edges_ne G' β hβ) σ
  set H := convexHull ℝ ((Finset.univ.image (kv β σ) : Finset _) :
        Set (Fin n → EuclideanSpace ℝ (Fin k))) with hH
  choose e he hsub using fun j => refineG_edge_sub G B (β j) (hβ j)
  have hHseg : ∀ p ∈ H, ∀ j, p j ∈ segment ℝ (e j).1 (e j).2 := by
    intro p hp j
    obtain ⟨w, hw0, -, hw1, rfl⟩ := (mem_convexHull_image_iff _ hinj _ p).1 hp
    exact hsub j (coord_mem_segment β σ w hw0 hw1 j)
  have hHcar : ∀ p ∈ H, ∀ j, p j ∈ G.carrier := fun p hp j =>
    Set.mem_biUnion (he j) (hHseg p hp j)
  obtain ⟨e0, he0⟩ := G.edges_nonempty
  let d0 : G.Pt := ⟨e0.1, Set.mem_biUnion he0 (left_mem_segment ℝ _ _)⟩
  let lift : (Fin n → EuclideanSpace ℝ (Fin k)) → Profile G n :=
    fun p j => if h : p j ∈ G.carrier then ⟨p j, h⟩ else d0
  have hlift : ∀ p ∈ H, ∀ j, ((lift p j : G.Pt) : EuclideanSpace ℝ (Fin k)) = p j := by
    intro p hp j; simp only [lift, dif_pos (hHcar p hp j)]
  have hlift_embed : ∀ x : Profile G n, lift (G.embed x) = x := by
    intro x; funext j
    show (if h : ((x j : G.Pt) : EuclideanSpace ℝ (Fin k)) ∈ G.carrier then _ else d0) = x j
    rw [dif_pos (x j).2]
    rfl
  let Ψ : Selector G n W → (Fin n → EuclideanSpace ℝ (Fin k)) → ℝ :=
    fun f p => G.dist (M (lift p)) (f.eval (lift p))
  -- Lipschitz estimate
  have hcoord : ∀ p ∈ H, ∀ q ∈ H, ∀ j, G.dist (lift p j) (lift q j) ≤ ‖p - q‖ := by
    intro p hp q hq j
    refine (dist_le_norm_of_seg G _ _ (e j) (he j) (by rw [hlift p hp]; exact hHseg p hp j)
      (by rw [hlift q hq]; exact hHseg q hq j)).trans ?_
    rw [hlift p hp, hlift q hq]
    exact norm_le_pi_norm (p - q) j
  have hΨlip : ∀ f, ∀ p ∈ H, ∀ q ∈ H, |Ψ f p - Ψ f q| ≤ (2 * n) * ‖p - q‖ := by
    intro f p hp q hq
    have hM : G.dist (M (lift p)) (M (lift q)) ≤ n * ‖p - q‖ := by
      refine (lip_chain G M hLip _ _).trans ?_
      calc ∑ j, G.dist (lift p j) (lift q j) ≤ ∑ _j : Fin n, ‖p - q‖ :=
            Finset.sum_le_sum (fun j _ => hcoord p hp q hq j)
        _ = n * ‖p - q‖ := by simp
    have hf : G.dist (f.eval (lift p)) (f.eval (lift q)) ≤ n * ‖p - q‖ := by
      cases f with
      | report i =>
        simp only [Selector.eval]
        refine (hcoord p hp q hq i).trans ?_
        have : (1 : ℝ) ≤ n := by
          have := i.2; exact_mod_cast (show 1 ≤ n by omega)
        nlinarith [norm_nonneg (p - q)]
      | const w hw =>
        simp only [Selector.eval]
        have h0 : G.dist w w ≤ 0 := by
          have := G.dist_le_walk w w 0 (fun _ => (w : EuclideanSpace ℝ (Fin k))) rfl rfl
            (fun j hj => absurd hj (by omega))
          simpa using this
        exact h0.trans (by positivity)
    have t1 := G.dist_triangle (M (lift p)) (M (lift q)) (f.eval (lift p))
    have t2 := G.dist_triangle (M (lift q)) (f.eval (lift q)) (f.eval (lift p))
    have t3 := G.dist_triangle (M (lift q)) (M (lift p)) (f.eval (lift q))
    have t4 := G.dist_triangle (M (lift p)) (f.eval (lift p)) (f.eval (lift q))
    rw [G.dist_comm (M (lift q)) (M (lift p))] at t3
    rw [G.dist_comm (f.eval (lift q)) (f.eval (lift p))] at t2
    have e2 : (2 * (n : ℝ)) * ‖p - q‖ = n * ‖p - q‖ + n * ‖p - q‖ := by ring
    simp only [Ψ]
    rw [abs_le, e2]
    constructor <;> linarith
  have hΨcont : ∀ f, ContinuousOn (Ψ f) H := by
    intro f
    have : LipschitzOnWith (Real.toNNReal (2 * n)) (Ψ f) H := by
      apply LipschitzOnWith.of_dist_le_mul
      intro p hp q hq
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
      exact hΨlip f p hp q hq
    exact this.continuousOn
  -- the generic set
  obtain ⟨R, hRH, hRconv, hHR, hRgen⟩ := facet_generic G' β hβ σ
  have hHne : H.Nonempty := ⟨kv β σ 0, subset_convexHull ℝ _
    (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ 0)))⟩
  have hRne : R.Nonempty := by
    obtain ⟨p, hp⟩ := hHne
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hHR hp
    rw [h, closure_empty] at this
    exact this
  obtain ⟨p0, hp0⟩ := hRne
  -- candidate selectors
  let cands : Finset (Selector G n W) :=
    Finset.univ.image Selector.report ∪ W.attach.image (fun w => Selector.const w.1 w.2)
  have hcands : ∀ f, f ∈ cands := by
    intro f
    cases f with
    | report i => exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    | const w hw => exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨w, hw⟩, Finset.mem_attach _ _, rfl⟩)
  have hΨnn : ∀ f p, 0 ≤ Ψ f p := fun f p => dist_nonneg' G _ _
  have hΨzero : ∀ f p, Ψ f p = 0 ↔ M (lift p) = f.eval (lift p) := by
    intro f p
    constructor
    · exact eq_of_dist_zero G _ _
    · intro h; simp only [Ψ]; rw [h]
      have h0 := dist_nonneg' G (f.eval (lift p)) (f.eval (lift p))
      have : G.dist (f.eval (lift p)) (f.eval (lift p)) ≤ 0 := by
        have := G.dist_le_walk (f.eval (lift p)) (f.eval (lift p)) 0
          (fun _ => ((f.eval (lift p) : G.Pt) : EuclideanSpace ℝ (Fin k))) rfl rfl
          (fun j hj => absurd hj (by omega))
        simpa using this
      linarith
  -- uniqueness of the matching selector on R
  have huniq : ∀ p ∈ R, ∀ f f' : Selector G n W, Ψ f p = 0 → Ψ f' p = 0 → f = f' := by
    intro p hp f f' h1 h2
    have hpH := hRH hp
    have heq : f.eval (lift p) = f'.eval (lift p) :=
      ((hΨzero f p).1 h1).symm.trans ((hΨzero f' p).1 h2)
    obtain ⟨hdist, hvert⟩ := hRgen p hp
    have hW : ∀ i, ∀ w ∈ W, p i ≠ (w : EuclideanSpace ℝ (Fin k)) := by
      intro i w hw hpw
      obtain ⟨e', he', hw'⟩ := refineG_vertex G B w (Finset.mem_image_of_mem _ hw) w.2
      rcases hw' with h | h
      · exact (hvert i e' he').1 (hpw.trans h)
      · exact (hvert i e' he').2 (hpw.trans h)
    cases f with
    | report i =>
      cases f' with
      | report j =>
        simp only [Selector.eval] at heq
        have := congrArg Subtype.val heq
        rw [hlift p hpH, hlift p hpH] at this
        by_contra hij
        exact hdist i j (fun h => hij (by rw [h])) this
      | const w hw =>
        simp only [Selector.eval] at heq
        have := congrArg Subtype.val heq
        rw [hlift p hpH] at this
        exact absurd this (hW i w hw)
    | const w hw =>
      cases f' with
      | report j =>
        simp only [Selector.eval] at heq
        have := congrArg Subtype.val heq.symm
        rw [hlift p hpH] at this
        exact absurd this (hW j w hw)
      | const w' hw' =>
        simp only [Selector.eval] at heq
        subst heq; rfl
  have hexist : ∀ p, ∃ f : Selector G n W, Ψ f p = 0 := by
    intro p
    rcases hval (lift p) with ⟨i, hi⟩ | hw
    · exact ⟨Selector.report i, (hΨzero _ p).2 hi⟩
    · exact ⟨Selector.const _ hw, (hΨzero _ p).2 rfl⟩
  obtain ⟨f0, hf0⟩ := hexist p0
  let Prd0 : (Fin n → EuclideanSpace ℝ (Fin k)) → ℝ := fun p => ∏ f ∈ cands.erase f0, Ψ f p
  let g : (Fin n → EuclideanSpace ℝ (Fin k)) → ℝ := fun p => Ψ f0 p - Prd0 p
  have hPrdnn : ∀ p, 0 ≤ Prd0 p := fun p => Finset.prod_nonneg (fun f _ => hΨnn f p)
  have hcase : ∀ p ∈ R, (Ψ f0 p = 0 ∧ 0 < Prd0 p) ∨ (0 < Ψ f0 p ∧ Prd0 p = 0) := by
    intro p hp
    obtain ⟨f, hf⟩ := hexist p
    by_cases hff : f = f0
    · subst hff
      left
      refine ⟨hf, lt_of_le_of_ne (hPrdnn p) (Ne.symm ?_)⟩
      rw [Finset.prod_ne_zero_iff]
      intro f' hf' h0
      exact (Finset.mem_erase.1 hf').1 (huniq p hp f' f h0 hf)
    · right
      refine ⟨lt_of_le_of_ne (hΨnn f0 p) (Ne.symm ?_), ?_⟩
      · intro h0; exact hff (huniq p hp f f0 hf h0)
      · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hff, hcands f⟩) hf
  have hgcont : ContinuousOn g R := by
    refine ((hΨcont f0).mono hRH).sub ?_
    exact continuousOn_finsetProd _ (fun f _ => (hΨcont f).mono hRH)
  have hgneg : ∀ p ∈ R, g p < 0 := by
    have hg0 : g p0 < 0 := by
      rcases hcase p0 hp0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [g]; linarith
      · exact absurd hf0 (ne_of_gt h1)
    intro p hp
    by_contra hc; push Not at hc
    have hivt := hRconv.isPreconnected.intermediate_value hp0 hp hgcont
    obtain ⟨q, hq, hq0⟩ := hivt ⟨hg0.le, hc⟩
    rcases hcase q hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [g] at hq0; linarith
    · simp only [g] at hq0; linarith
  have hR0 : ∀ p ∈ R, Ψ f0 p = 0 := by
    intro p hp
    rcases hcase p hp with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · have := hgneg p hp; simp only [g] at this; linarith
  -- extend to the closure
  have hHclosed : IsClosed H :=
    ((Set.toFinite _).isCompact_convexHull ℝ).isClosed
  have hZ : IsClosed (H ∩ Ψ f0 ⁻¹' {0}) :=
    (hΨcont f0).preimage_isClosed_of_isClosed hHclosed isClosed_singleton
  have hH0 : ∀ p ∈ H, Ψ f0 p = 0 := by
    intro p hp
    have hRZ : R ⊆ H ∩ Ψ f0 ⁻¹' {0} := fun q hq => ⟨hRH hq, hR0 q hq⟩
    exact ((closure_minimal hRZ hZ) (hHR hp)).2
  refine ⟨f0, fun x hx => ?_⟩
  have := (hΨzero f0 (G.embed x)).1 (hH0 _ hx)
  rwa [hlift_embed] at this

end SPFGKuhn

namespace SPFGKuhn
open SPFacilityGraph
variable {k n : ℕ}

theorem attribution_of_lip (G : MetricGraph k) (M : Profile G n → G.Pt) (W : Finset G.Pt)
    (hLip : ∀ (x : Profile G n) (i : Fin n) (y : G.Pt),
      G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i))
    (hval : ∀ x, (∃ i, M x = x i) ∨ M x ∈ W) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k)),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K := by
  classical
  set B : Finset (EuclideanSpace ℝ (Fin k)) := W.image Subtype.val with hB
  set G' := refineG G B with hG'
  refine ⟨kuhnComplex G' n, ⟨kuhn_faces_finite G', ?_, ?_⟩, ?_⟩
  · rw [kuhn_space]; exact range_embed_eq G' G (refineG_carrier G B)
  · intro s hs
    obtain ⟨β, σ, hβ, rfl⟩ := facet_eq G' s hs
    choose e he hsub using fun j => refineG_edge_sub G B (β j) (hβ j)
    refine ⟨e, he, fun p hp j => ?_⟩
    obtain ⟨w, hw0, -, hw1, rfl⟩ :=
      (mem_convexHull_image_iff _ (kv_injective β (edges_ne G' β hβ) σ) _ p).1 hp
    exact hsub j (coord_mem_segment β σ w hw0 hw1 j)
  · have : ∀ s : (kuhnComplex G' n).facets, ∃ f : Selector G n W, ∀ x : Profile G n,
        G.embed x ∈ convexHull ℝ (s.1 : Set (Fin n → EuclideanSpace ℝ (Fin k))) → M x = f.eval x := by
      intro s
      obtain ⟨β, σ, hβ, hs⟩ := facet_eq G' s.1 s.2
      rw [hs]
      exact facet_selector G M W hLip hval β hβ σ
    choose sel hsel using this
    exact ⟨sel, hsel⟩

end SPFGKuhn


open SPFacilityGraph in
theorem solution {k n : ℕ} (G : MetricGraph k) (M : Profile G n → G.Pt)
    (W : Finset G.Pt)
    (hLip : ∀ (x : Profile G n) (i : Fin n) (y : G.Pt),
      G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i))
    (hval : ∀ x : Profile G n, (∃ i, M x = x i) ∨ M x ∈ W) :
    ∃ K : Geometry.SimplicialComplex ℝ (Fin n → EuclideanSpace ℝ (Fin k)),
      IsEdgeTriangulation G n K ∧ HasDetAttribution G M W K :=
  SPFGKuhn.attribution_of_lip G M W hLip hval
