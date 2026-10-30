-- Prove2me | solution 1 for PDASNewton.MMatrix.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T03:47:34.589737+00:00
-- url     : https://prove2.me/submissions/67caae55-5919-477c-a2f0-1ab0e1afb7b2

import Definitions.Def_PDASNewton_MMatrix_Setting


namespace PDASNewton.MMatrix.PDFresh

theorem scalar_complementarity (c u p l : ℝ) (hc : 0 < c) :
    l - max 0 (l + c * (u - p)) = 0 ↔
      0 ≤ l ∧ u ≤ p ∧ (u = p ∨ l = 0) := by
  constructor
  · intro h
    have he : l = max 0 (l + c * (u - p)) := sub_eq_zero.mp h
    have hl : 0 ≤ l := (le_max_left _ _).trans he.ge
    have hs : l + c * (u - p) ≤ l := (le_max_right _ _).trans he.ge
    have hup : u ≤ p := by nlinarith
    refine ⟨hl, hup, ?_⟩
    by_cases hz : l = 0
    · exact Or.inr hz
    · left
      have hp : 0 < l := lt_of_le_of_ne hl (Ne.symm hz)
      have hm : max 0 (l + c * (u - p)) = l + c * (u - p) := by
        apply max_eq_right
        by_contra hh
        have hh' : l + c * (u - p) ≤ 0 := le_of_not_ge hh
        rw [max_eq_left hh'] at he
        linarith
      rw [hm] at he
      nlinarith
  · rintro ⟨hl, hup, h | h⟩
    · subst u
      simp [max_eq_right hl]
    · subst l
      have hs : c * (u - p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hup)
      simp [max_eq_left hs]

end PDASNewton.MMatrix.PDFresh


namespace PDASNewton.MMatrix.PDFresh
open Matrix

theorem positive_weight {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsMMatrix A) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ A *ᵥ w = 1 := by
  let w : Fin n → ℝ := A⁻¹ *ᵥ 1
  have hw (i : Fin n) : 0 ≤ w i := by
    dsimp [w, mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hA.2.2 i j) (by norm_num)
  have hpos (i : Fin n) : 0 < w i := by
    by_contra hn
    have hz : w i = 0 := le_antisymm (le_of_not_gt hn) (hw i)
    have hs : ∑ j, A⁻¹ i j = 0 := by simpa [w, mulVec, dotProduct] using hz
    have hrow (j : Fin n) : A⁻¹ i j = 0 := by
      have hj : A⁻¹ i j ≤ ∑ k, A⁻¹ i k := Finset.single_le_sum (fun k _ => hA.2.2 i k) (Finset.mem_univ j)
      exact le_antisymm (by simpa [hs] using hj) (hA.2.2 i j)
    have hi := congrArg (fun B : Matrix (Fin n) (Fin n) ℝ => B i i) (nonsing_inv_mul A hA.1)
    simp [mul_apply, hrow] at hi
  refine ⟨w, hpos, ?_⟩
  dsimp [w]
  rw [mulVec_mulVec, mul_nonsing_inv A hA.1, one_mulVec]

end PDASNewton.MMatrix.PDFresh


namespace PDASNewton.MMatrix.PDFresh
open Matrix

theorem maximum_principle {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsMMatrix A) (d : Fin n → ℝ)
    (h : ∀ i, 0 < d i → (A *ᵥ d) i ≤ 0) : d ≤ 0 := by
  obtain ⟨w, hw, hAw⟩ := positive_weight A hA
  intro j
  change d j ≤ 0
  by_contra hj
  have hjp : 0 < d j := lt_of_not_ge hj
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun k => d k / w k)
    ⟨j, Finset.mem_univ j⟩
  let t := d i / w i
  have ht : 0 < t := lt_of_lt_of_le (div_pos hjp (hw j)) (hi j (Finset.mem_univ j))
  have hdi : d i = t * w i := by dsimp [t]; rw [div_mul_cancel₀ _ (ne_of_gt (hw i))]
  have hd (k : Fin n) : d k ≤ t * w k := (div_le_iff₀ (hw k)).mp (hi k (Finset.mem_univ k))
  have hsum : t * (A *ᵥ w) i ≤ (A *ᵥ d) i := by
    simp only [mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : i = k
    · subst k
      rw [hdi]
      nlinarith [le_refl (t * (A i i * w i))]
    · calc
        t * (A i k * w k) = A i k * (t * w k) := by ring
        _ ≤ A i k * d k := mul_le_mul_of_nonpos_left (hd k) (hA.2.1 i k hk)
  have hai : (A *ᵥ w) i = 1 := congrFun hAw i
  rw [hai, mul_one] at hsum
  have hdp : 0 < d i := by rw [hdi]; exact mul_pos ht (hw i)
  linarith [h i hdp]

end PDASNewton.MMatrix.PDFresh


namespace PDASNewton.MMatrix.PDFresh
open Matrix PDASNewton.Local

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {f ψ : Fin n → ℝ} {c : ℝ}

theorem solution_properties {u l : Fin n → ℝ} (hc : 0 < c)
    (hs : IsSolution A f ψ c u l) (i : Fin n) :
    0 ≤ l i ∧ u i ≤ ψ i ∧ (u i = ψ i ∨ l i = 0) :=
  (scalar_complementarity c (u i) (ψ i) (l i) hc).mp (hs.2 i)

theorem step_output_alternative {u l v m : Fin n → ℝ}
    (hs : IsStep A f ψ c u l v m) (i : Fin n) : v i = ψ i ∨ m i = 0 := by
  by_cases h : 0 < l i + c * (u i - ψ i)
  · exact Or.inl (hs.2.1 i h)
  · exact Or.inr (hs.2.2 i (le_of_not_gt h))

theorem stationary_solution {u l : Fin n → ℝ}
    (hs : IsStep A f ψ c u l u l) : IsSolution A f ψ c u l := by
  refine ⟨hs.1, fun i => ?_⟩
  by_cases h : 0 < l i + c * (u i - ψ i)
  · have hu := hs.2.1 i h
    rw [hu] at h ⊢
    simp only [sub_self, mul_zero, add_zero] at h ⊢
    rw [max_eq_right h.le, sub_self]
  · have hn := le_of_not_gt h
    have hl := hs.2.2 i hn
    rw [max_eq_left hn, hl, sub_self]

theorem solution_self_step {u l : Fin n → ℝ} (hc : 0 < c)
    (hs : IsSolution A f ψ c u l) : IsStep A f ψ c u l u l := by
  refine ⟨hs.1, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨_, hu, he | he⟩ := solution_properties hc hs i
    · exact he
    · rw [he] at hi
      have := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr hu)
      linarith
  · have he := hs.2 i
    rw [max_eq_left hi] at he
    simpa using he

theorem equilibrium_difference {u l v m : Fin n → ℝ}
    (hu : A *ᵥ u + l = f) (hv : A *ᵥ v + m = f) :
    A *ᵥ (u - v) = m - l := by
  rw [mulVec_sub]
  ext i
  have h1 := congrFun hu i
  have h2 := congrFun hv i
  simp only [Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
  linarith

theorem output_unique (hA : IsMMatrix A)
    {u l u' l' v m v' m' : Fin n → ℝ}
    (hs : IsStep A f ψ c u l v m) (ht : IsStep A f ψ c u' l' v' m')
    (he : activeSet c ψ u l = activeSet c ψ u' l') : v = v' ∧ m = m' := by
  have hmask (i : Fin n) : (0 < l i + c * (u i - ψ i)) ↔
      (0 < l' i + c * (u' i - ψ i)) := by
    have hh := Finset.ext_iff.mp he i
    simpa [activeSet] using hh
  have one {a b la lb : Fin n → ℝ} (ha : A *ᵥ a + la = f)
      (hb : A *ᵥ b + lb = f) (h : ∀ i, a i ≠ b i → la i = 0 ∧ lb i = 0) : a ≤ b := by
    have hd := equilibrium_difference ha hb
    have hh := maximum_principle hA (a - b) (by
      intro i hi
      have hab : a i ≠ b i := by
        intro heq
        simp [Pi.sub_apply, heq] at hi
      obtain ⟨hla, hlb⟩ := h i hab
      rw [hd]
      simp [hla, hlb])
    intro i
    exact sub_nonpos.mp (hh i)
  have hzero (i : Fin n) (hi : v i ≠ v' i) : m i = 0 ∧ m' i = 0 := by
    by_cases hp : 0 < l i + c * (u i - ψ i)
    · exact False.elim (hi ((hs.2.1 i hp).trans (ht.2.1 i ((hmask i).mp hp)).symm))
    · exact ⟨hs.2.2 i (le_of_not_gt hp), ht.2.2 i (le_of_not_gt (fun h => hp ((hmask i).mpr h)))⟩
  have hv : v = v' := le_antisymm (one hs.1 ht.1 hzero)
    (one ht.1 hs.1 (fun i hi => (hzero i (Ne.symm hi)).symm))
  refine ⟨hv, ?_⟩
  have hd := equilibrium_difference hs.1 ht.1
  rw [hv, sub_self, mulVec_zero] at hd
  exact (sub_eq_zero.mp hd.symm).symm

theorem solution_unique (hc : 0 < c) (hA : IsMMatrix A)
    {u l v m : Fin n → ℝ} (hs : IsSolution A f ψ c u l)
    (ht : IsSolution A f ψ c v m) : u = v ∧ l = m := by
  have one {a la b lb : Fin n → ℝ} (ha : IsSolution A f ψ c a la)
      (hb : IsSolution A f ψ c b lb) : a ≤ b := by
    have hd := equilibrium_difference ha.1 hb.1
    have hh := maximum_principle hA (a - b) (by
      intro i hi
      obtain ⟨hla, hupa, _⟩ := solution_properties hc ha i
      obtain ⟨_, _, he | he⟩ := solution_properties hc hb i
      · simp only [Pi.sub_apply] at hi
        rw [he] at hi
        linarith
      · rw [hd]
        simp only [Pi.sub_apply, he, zero_sub]
        exact neg_nonpos.mpr hla)
    intro i
    exact sub_nonpos.mp (hh i)
  have hu := le_antisymm (one hs ht) (one ht hs)
  refine ⟨hu, ?_⟩
  have hd := equilibrium_difference hs.1 ht.1
  rw [hu, sub_self, mulVec_zero] at hd
  exact (sub_eq_zero.mp hd.symm).symm

theorem run_equilibrium {y l : ℕ → Fin n → ℝ} (hr : IsRun A f ψ c y l)
    {k : ℕ} (hk : 1 ≤ k) : A *ᵥ y k + l k = f := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact (hr j).1

theorem run_alternative {y l : ℕ → Fin n → ℝ} (hr : IsRun A f ψ c y l)
    {k : ℕ} (hk : 1 ≤ k) (i : Fin n) : y k i = ψ i ∨ l k i = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact step_output_alternative (hr j) i

theorem run_decreasing (hc : 0 < c) (hA : IsMMatrix A)
    {y l : ℕ → Fin n → ℝ} (hr : IsRun A f ψ c y l)
    {k : ℕ} (hk : 1 ≤ k) : y (k + 1) ≤ y k := by
  have hd := equilibrium_difference (hr k).1 (run_equilibrium hr hk)
  have hh := maximum_principle hA (y (k + 1) - y k) (by
    intro i hi
    simp only [Pi.sub_apply] at hi
    have hin : l k i + c * (y k i - ψ i) ≤ 0 := by
      by_contra hn
      have hp := lt_of_not_ge hn
      have hv := (hr k).2.1 i hp
      obtain he | he := run_alternative hr hk i
      · rw [he, hv] at hi
        linarith
      · rw [he] at hp
        have hneg : c * (y k i - ψ i) < 0 := mul_neg_of_pos_of_neg hc (by linarith)
        linarith
    have hl : l k i ≤ 0 := by
      obtain he | he := run_alternative hr hk i
      · rw [he] at hin
        simpa using hin
      · exact he.le
    rw [hd]
    simpa [(hr k).2.2 i hin] using hl)
  intro i
  exact sub_nonpos.mp (hh i)

theorem run_lower (hc : 0 < c) (hA : IsMMatrix A)
    {u m : Fin n → ℝ} (hs : IsSolution A f ψ c u m)
    {y l : ℕ → Fin n → ℝ} (hr : IsRun A f ψ c y l) (k : ℕ) : u ≤ y (k + 1) := by
  have hd := equilibrium_difference hs.1 (hr k).1
  have hh := maximum_principle hA (u - y (k + 1)) (by
    intro i hi
    obtain ⟨hm, hu, _⟩ := solution_properties hc hs i
    have hin : l k i + c * (y k i - ψ i) ≤ 0 := by
      by_contra hn
      have he := (hr k).2.1 i (lt_of_not_ge hn)
      simp only [Pi.sub_apply] at hi
      rw [he] at hi
      linarith
    rw [hd]
    simpa [(hr k).2.2 i hin] using neg_nonpos.mpr hm)
  intro i
  exact sub_nonpos.mp (hh i)

theorem run_feasible (hc : 0 < c) (hA : IsMMatrix A)
    {y l : ℕ → Fin n → ℝ} (hr : IsRun A f ψ c y l)
    {k : ℕ} (hk : 2 ≤ k) : y k ≤ ψ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hj : 1 ≤ j := by omega
  intro i
  by_cases h : y j i ≤ ψ i
  · exact (run_decreasing hc hA hr hj i).trans h
  · have hp : ψ i < y j i := lt_of_not_ge h
    obtain he | he := run_alternative hr hj i
    · exact False.elim (h he.le)
    · have hs : 0 < l j i + c * (y j i - ψ i) := by
        rw [he, zero_add]
        exact mul_pos hc (sub_pos.mpr hp)
      exact ((hr j).2.1 i hs).le

end PDASNewton.MMatrix.PDFresh


namespace PDASNewton.MMatrix.PDFresh
open Matrix PDASNewton.Local Filter Topology

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {f ψ : Fin n → ℝ} {c : ℝ}

theorem run_exact_from_card (hc : 0 < c) (hA : IsMMatrix A)
    {u m : Fin n → ℝ} (hs : IsSolution A f ψ c u m)
    {y l : ℕ → Fin n → ℝ} (hr : IsRun A f ψ c y l) :
    ∀ k, 2 ^ n ≤ k → y k = u ∧ l k = m := by
  classical
  have ha : Antitone (fun k : ℕ => y (k + 1)) := by
    apply antitone_nat_of_succ_le
    intro k
    exact run_decreasing hc hA hr (by omega)
  let mask : Fin (2 ^ n + 1) → Finset (Fin n) :=
    fun k => activeSet c ψ (y k) (l k)
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt mask (by simp)
  have ordered : ∃ i j : Fin (2 ^ n + 1), i < j ∧ mask i = mask j := by
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact ⟨i, j, hh, he⟩
    · exact ⟨j, i, hh, he.symm⟩
  obtain ⟨i, j, hij, he⟩ := ordered
  have houtputs := output_unique hA (hr (i : ℕ)) (hr (j : ℕ)) he
  have hsucc : y ((i : ℕ) + 2) = y ((i : ℕ) + 1) := by
    apply le_antisymm
    · exact run_decreasing hc hA hr (by omega)
    · rw [houtputs.1]
      exact ha (by have hi : (i : ℕ) < (j : ℕ) := hij; omega)
  have hmul : l ((i : ℕ) + 2) = l ((i : ℕ) + 1) := by
    have hh := equilibrium_difference (hr ((i : ℕ) + 1)).1 (hr (i : ℕ)).1
    have hz : y ((i : ℕ) + 1 + 1) = y ((i : ℕ) + 1) := by simpa [Nat.add_assoc] using hsucc
    rw [hz, sub_self, mulVec_zero] at hh
    exact (sub_eq_zero.mp hh.symm).symm
  have hstationary : IsStep A f ψ c (y ((i : ℕ) + 1)) (l ((i : ℕ) + 1))
      (y ((i : ℕ) + 1)) (l ((i : ℕ) + 1)) := by
    have hh := hr ((i : ℕ) + 1)
    simpa only [show (i : ℕ) + 1 + 1 = (i : ℕ) + 2 by omega, hsucc, hmul] using hh
  have hstart := solution_unique hc hA (stationary_solution hstationary) hs
  have htail : ∀ k, (i : ℕ) + 1 ≤ k → y k = u ∧ l k = m := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hstart
    | succ k hk ih =>
      apply output_unique hA (hr k) (solution_self_step hc hs)
      rw [ih.1, ih.2]
  intro k hk
  apply htail
  have hi : (i : ℕ) < (j : ℕ) := hij
  have hj := j.isLt
  omega

theorem run_tendsto (hc : 0 < c) (hA : IsMMatrix A)
    {u m : Fin n → ℝ} (hs : IsSolution A f ψ c u m)
    {y l : ℕ → Fin n → ℝ} (hr : IsRun A f ψ c y l) :
    Tendsto (fun k => (y k, l k)) atTop (𝓝 (u, m)) := by
  have he : (fun k => (y k, l k)) =ᶠ[atTop] (fun _ => (u, m)) := by
    filter_upwards [eventually_ge_atTop (2 ^ n)] with k hk
    obtain ⟨hy, hl⟩ := run_exact_from_card hc hA hs hr k hk
    simp only [hy, hl]
  exact (tendsto_congr' he).mpr tendsto_const_nhds

end PDASNewton.MMatrix.PDFresh


namespace PDASNewton.MMatrix.PDFresh
open Matrix Filter Topology

theorem native_theorem_3_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (ystar lamstar : Fin n → ℝ)
    (hsol : PDASNewton.Local.IsSolution A f ψ c ystar lamstar) (y lam : ℕ → Fin n → ℝ)
    (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    Tendsto (fun k => (y k, lam k)) atTop (𝓝 (ystar, lamstar)) ∧
      (∀ k, 1 ≤ k → ystar ≤ y (k + 1) ∧ y (k + 1) ≤ y k) ∧
      (∀ k, 2 ≤ k → y k ≤ ψ) := by
  refine ⟨run_tendsto hc hA hsol hrun, ?_, ?_⟩
  · intro k hk
    exact ⟨run_lower hc hA hsol hrun k, run_decreasing hc hA hrun hk⟩
  · intro k hk
    exact run_feasible hc hA hrun hk

end PDASNewton.MMatrix.PDFresh

open Matrix Filter Topology

namespace PDASNewton.MMatrix

theorem theorem_3_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (ystar lamstar : Fin n → ℝ)
    (hsol : PDASNewton.Local.IsSolution A f ψ c ystar lamstar) (y lam : ℕ → Fin n → ℝ)
    (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    Tendsto (fun k => (y k, lam k)) atTop (𝓝 (ystar, lamstar)) ∧
      (∀ k, 1 ≤ k → ystar ≤ y (k + 1) ∧ y (k + 1) ≤ y k) ∧
      (∀ k, 2 ≤ k → y k ≤ ψ) := by
  exact PDFresh.native_theorem_3_2 A f ψ c hc hA ystar lamstar hsol y lam hrun

end PDASNewton.MMatrix

open PDASNewton.MMatrix

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (ystar lamstar : Fin n → ℝ)
    (hsol : PDASNewton.Local.IsSolution A f ψ c ystar lamstar) (y lam : ℕ → Fin n → ℝ)
    (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    Tendsto (fun k => (y k, lam k)) atTop (𝓝 (ystar, lamstar)) ∧
      (∀ k, 1 ≤ k → ystar ≤ y (k + 1) ∧ y (k + 1) ≤ y k) ∧
      (∀ k, 2 ≤ k → y k ≤ ψ) := by
  exact PDASNewton.MMatrix.theorem_3_2 A f ψ c hc hA ystar lamstar hsol y lam hrun

