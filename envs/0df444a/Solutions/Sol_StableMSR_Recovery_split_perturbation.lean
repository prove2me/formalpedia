-- Prove2me | solution 1 for StableMSR.Recovery.split_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T14:01:59.315734+00:00
-- url     : https://prove2.me/submissions/226dfec9-eba0-439b-b98c-9f0c1229091f

import Definitions.Def_StableMSR_Recovery_Geometry

set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery

namespace SplitAux

lemma radius_le_ecc {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {c : Point n} (hc : c ∈ C) :
    radius d C ≤ eccentricity d C c := by
  classical
  rw [radius, dif_pos ⟨c, hc⟩]
  exact Finset.inf'_le _ hc

lemma dist_le_ecc {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (c : Point n) {x : Point n} (hx : x ∈ C) :
    d c x ≤ eccentricity d C c := by
  classical
  rw [eccentricity, dif_pos ⟨x, hx⟩]
  exact Finset.le_sup' _ hx

lemma ecc_le {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) (c : Point n) {a : ℝ}
    (ha : ∀ x ∈ C, d c x ≤ a) : eccentricity d C c ≤ a := by
  classical
  rw [eccentricity, dif_pos hC]
  exact Finset.sup'_le hC _ ha

lemma ecc_le_iff {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) (c : Point n) (a : ℝ) :
    eccentricity d C c ≤ a ↔ ∀ x ∈ C, d c x ≤ a := by
  constructor
  · intro h x hx
    exact (dist_le_ecc d c hx).trans h
  · exact ecc_le d hC c

lemma radius_le {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {c : Point n} (hc : c ∈ C) {a : ℝ}
    (ha : ∀ x ∈ C, d c x ≤ a) : radius d C ≤ a :=
  (radius_le_ecc d hc).trans (ecc_le d ⟨c, hc⟩ c ha)

lemma le_radius {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) {a : ℝ}
    (ha : ∀ c ∈ C, a ≤ eccentricity d C c) : a ≤ radius d C := by
  classical
  rw [radius, dif_pos hC]
  exact Finset.le_inf' hC _ ha

lemma exists_optimal_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, heq⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  exact ⟨c, hc, by simpa [radius, hC] using heq.symm⟩

lemma exists_far {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} {x : Point n} (hx : x ∈ C) :
    ∃ y ∈ C, radius d C ≤ d x y := by
  classical
  have hC : C.Nonempty := ⟨x, hx⟩
  obtain ⟨y, hy, heq⟩ := Finset.exists_mem_eq_sup' hC (d x)
  refine ⟨y, hy, ?_⟩
  have h := radius_le_ecc d hx
  simpa [eccentricity, hC, heq] using h

lemma radius_pos {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) {C : Cluster n} (hC : 2 ≤ C.card) :
    0 < radius d C := by
  classical
  have hC' : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc, hecc⟩ := exists_optimal_center d hC'
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) c
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hcy : 0 < d c y := by
    rw [← hm c y]
    exact dist_pos.mpr (Ne.symm hyc)
  exact lt_of_lt_of_le hcy ((dist_le_ecc d c hy).trans hecc.le)

end SplitAux

private lemma choose_split_center {n : ℕ} (d : Point n → Point n → ℝ)
    (C : Cluster n) (r : ℝ) (hr : 0 < r)
    (hsymm : ∀ x y, d x y = d y x) (hself : ∀ x, d x x = 0)
    (hneigh : ∀ x ∈ C, ∃ y ∈ C, r ≤ d x y)
    (u : Point n) (hu : u ∈ C) (huc : ∀ y ∈ C, d u y ≤ r) :
    ∃ c ∈ C, ∃ p ∈ C, p ≠ c ∧ (∀ y ∈ C, d c y ≤ r) ∧
      ∀ x ∈ C, ∃ y ∈ C, r ≤ d x y ∧
        (x ≠ c ∨ y = p) ∧ (y ≠ c ∨ x = p) := by
  classical
  by_cases hbad : ∃ v ∈ C, r ≤ d u v ∧ ∀ w ∈ C, r ≤ d v w → w = u
  · obtain ⟨v, hv, huv, hvonly⟩ := hbad
    have huvne : u ≠ v := by
      intro h
      have := hself v
      subst u
      linarith
    have hvc : ∀ y ∈ C, d v y ≤ r := by
      intro y hy
      by_cases hyu : y = u
      · subst y
        rw [hsymm]
        exact huc v hv
      · by_contra h
        exact hyu (hvonly y hy (le_of_lt (lt_of_not_ge h)))
    refine ⟨v, hv, u, hu, huvne, hvc, ?_⟩
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hneigh x hx
    refine ⟨y, hy, hxy, ?_, ?_⟩
    · by_cases hxv : x = v
      · right
        subst x
        exact hvonly y hy hxy
      · exact Or.inl hxv
    · by_cases hyv : y = v
      · right
        subst y
        exact hvonly x hx (by rw [hsymm]; exact hxy)
      · exact Or.inl hyv
  · obtain ⟨p, hp, hup⟩ := hneigh u hu
    have hpu : p ≠ u := by
      intro h
      subst p
      rw [hself] at hup
      linarith
    refine ⟨u, hu, p, hp, hpu, huc, ?_⟩
    intro x hx
    by_cases hxu : x = u
    · subst x
      exact ⟨p, hp, hup, Or.inr rfl, Or.inl hpu⟩
    by_cases hxp : x = p
    · subst x
      exact ⟨u, hu, by rw [hsymm]; exact hup, Or.inl hpu, Or.inr rfl⟩
    have hother : ∃ y ∈ C, r ≤ d x y ∧ y ≠ u := by
      by_contra hn
      have honly : ∀ y ∈ C, r ≤ d x y → y = u := by
        intro y hy hxy
        by_contra hne
        exact hn ⟨y, hy, hxy, hne⟩
      obtain ⟨y, hy, hxy⟩ := hneigh x hx
      have hyu : y = u := honly y hy hxy
      apply hbad
      refine ⟨x, hx, ?_, honly⟩
      rw [hsymm, ← hyu]
      exact hxy
    obtain ⟨y, hy, hxy, hyu⟩ := hother
    exact ⟨y, hy, hxy, Or.inl hxu, Or.inl hyu⟩

theorem solution {n : ℕ} (d : Point n → Point n → ℝ)
    (hd : IsMetricArray d) (γ : ℝ) (hγ : 1 < γ)
    (C : Cluster n) (hC : 2 ≤ C.card) :
    ∃ c p : Point n, OptimalCenter d C c ∧ p ∈ C ∧ p ≠ c ∧
      ∃ d' : Point n → Point n → ℝ, Perturbation d γ d' ∧
        (∀ x y, ¬ (x ∈ C ∧ y ∈ C) → d' x y = d x y) ∧
        radius d' C = γ * radius d C ∧ radius d' (C.erase p) ≤ radius d C := by
  classical
  have hCn : C.Nonempty := Finset.card_pos.mp (by omega)
  let r := radius d C
  have hr : 0 < r := SplitAux.radius_pos d hd hC
  have hg0 : 0 ≤ γ := by linarith
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hsymm : ∀ x y, d x y = d y x := by
    intro x y
    rw [← hm x y, ← hm y x]
    exact dist_comm x y
  have hself : ∀ x, d x x = 0 := by
    intro x
    rw [← hm x x]
    exact dist_self x
  have hnonneg : ∀ x y, 0 ≤ d x y := by
    intro x y
    rw [← hm x y]
    exact dist_nonneg
  obtain ⟨u, hu, hueq⟩ := SplitAux.exists_optimal_center d hCn
  have huc : ∀ y ∈ C, d u y ≤ r := by
    intro y hy
    exact (SplitAux.dist_le_ecc d u hy).trans hueq.le
  have hneigh : ∀ x ∈ C, ∃ y ∈ C, r ≤ d x y := by
    intro x hx
    exact SplitAux.exists_far d hx
  obtain ⟨c, hc, p, hp, hpc, hcc, hwitness⟩ :=
    choose_split_center d C r hr hsymm hself hneigh u hu huc
  have hcopt : OptimalCenter d C c := by
    refine ⟨hc, ?_⟩
    exact le_antisymm (SplitAux.ecc_le d hCn c hcc) (SplitAux.radius_le_ecc d hc)
  let S : Point n → Point n → Prop := fun x y =>
    x ∈ C ∧ y ∈ C ∧ (x ≠ c ∨ y = p) ∧ (y ≠ c ∨ x = p)
  have hSsymm : ∀ x y, S x y ↔ S y x := by
    intro x y
    dsimp [S]
    constructor <;> rintro ⟨ha, hb, hc', hd'⟩ <;> exact ⟨hb, ha, hd', hc'⟩
  let d' : Point n → Point n → ℝ := fun x y => if S x y then γ * d x y else d x y
  have hupper : ∀ x y, d x y ≤ d' x y ∧ d' x y ≤ γ * d x y := by
    intro x y
    have hscale : d x y ≤ γ * d x y := by nlinarith [hnonneg x y]
    dsimp [d']
    split_ifs <;> exact ⟨by first | exact hscale | rfl, by first | exact hscale | rfl⟩
  have hpert : Perturbation d γ d' := by
    refine ⟨?_, hupper⟩
    intro x y
    simp only [d', hSsymm x y, hsymm x y]
  have houtside : ∀ x y, ¬ (x ∈ C ∧ y ∈ C) → d' x y = d x y := by
    intro x y hxy
    have hnS : ¬ S x y := fun h => hxy ⟨h.1, h.2.1⟩
    simp only [d', if_neg hnS]
  have hrup : radius d' C ≤ γ * r := by
    apply SplitAux.radius_le d' hc
    intro y hy
    exact (hupper c y).2.trans (mul_le_mul_of_nonneg_left (hcc y hy) hg0)
  have hrlo : γ * r ≤ radius d' C := by
    apply SplitAux.le_radius d' hCn
    intro x hx
    obtain ⟨y, hy, hxy, ha, hb⟩ := hwitness x hx
    have hS : S x y := ⟨hx, hy, ha, hb⟩
    have hscaled : d' x y = γ * d x y := by simp only [d', if_pos hS]
    have hl : γ * r ≤ d' x y := by
      rw [hscaled]
      exact mul_le_mul_of_nonneg_left hxy hg0
    exact hl.trans (SplitAux.dist_le_ecc d' x hy)
  have herase : radius d' (C.erase p) ≤ r := by
    have hce : c ∈ C.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpc, hc⟩
    apply SplitAux.radius_le d' hce
    intro y hy
    obtain ⟨hyp, hyC⟩ := Finset.mem_erase.mp hy
    have hnS : ¬ S c y := by
      intro h
      rcases h.2.2.1 with hcc' | hyp'
      · exact hcc' rfl
      · exact hyp hyp'
    simpa only [d', if_neg hnS] using hcc y hyC
  exact ⟨c, p, hcopt, hp, hpc, d', hpert, houtside, le_antisymm hrup hrlo, herase⟩
