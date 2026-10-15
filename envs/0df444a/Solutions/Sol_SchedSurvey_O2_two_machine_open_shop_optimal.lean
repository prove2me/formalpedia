-- Prove2me | solution 1 for SchedSurvey.O2.two_machine_open_shop_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:13:01.723862+00:00
-- url     : https://prove2.me/submissions/47693b25-f40a-4218-9279-86a606164adc

import Mathlib
import Definitions.Def_SchedSurvey_O2_Model

set_option autoImplicit false

open SchedSurvey.O2

theorem os2_symm {s p s' p' : ℝ} (h : NoOverlap s p s' p') : NoOverlap s' p' s p := Or.symm h

theorem os2_mono {s P s' p' t q t' q' : ℝ} (h : NoOverlap s P s' p') (h1 : s ≤ t) (h2 : t + q ≤ s + P)
    (h3 : s' ≤ t') (h4 : t' + q' ≤ s' + p') : NoOverlap t q t' q' := by
  unfold NoOverlap at *
  rcases h with h | h
  · left; linarith
  · right; linarith

/-- necessity of the load bound: disjoint intervals inside `[0,T]` have total length at most `T`. -/
theorem os2_sum_le {n : ℕ} (s p : Fin n → ℝ) (T : ℝ) (hT : 0 ≤ T) (hp : ∀ j, 0 ≤ p j)
    (h0 : ∀ j, 0 ≤ s j) (hc : ∀ j, s j + p j ≤ T)
    (hd : ∀ j k, j ≠ k → NoOverlap (s j) (p j) (s k) (p k)) : ∑ j, p j ≤ T := by
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) (fun j => Set.Ico (s j) (s j + p j)) := by
    intro j _ k _ hjk
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    simp only [Set.mem_Ico] at hx hx'
    unfold NoOverlap at hd
    rcases hd j k hjk with h | h
    · linarith [hx.1, hx.2, hx'.1, hx'.2]
    · linarith [hx.1, hx.2, hx'.1, hx'.2]
  have hmeas : ∀ j ∈ (Finset.univ : Finset (Fin n)), MeasurableSet (Set.Ico (s j) (s j + p j)) :=
    fun j _ => measurableSet_Ico
  have h1 := MeasureTheory.measure_biUnion_finset (μ := MeasureTheory.volume) hdis hmeas
  have h2 : (⋃ j ∈ (Finset.univ : Finset (Fin n)), Set.Ico (s j) (s j + p j)) ⊆ Set.Ico 0 T := by
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ico] at hx
    obtain ⟨j, _, hj1, hj2⟩ := hx
    exact ⟨by linarith [h0 j], by linarith [hc j, hp j]⟩
  have h3 := MeasureTheory.measure_mono (μ := MeasureTheory.volume) h2
  rw [h1] at h3
  simp only [Real.volume_Ico] at h3
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by linarith [hp j])] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h3
  have h5 : ∑ j ∈ (Finset.univ : Finset (Fin n)), (s j + p j - s j) = ∑ j, p j := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h5] at h4
  linarith

/-- explicit one-job schedules -/
theorem os2_gen1 {n : ℕ} (J : Finset (Fin n)) (x : Fin n) (hJ : J = {x}) (a b : Fin n → ℝ)
    (t1 t2 : ℝ) (h0 : 0 ≤ t1 ∧ 0 ≤ t2) (hx : NoOverlap t1 (a x) t2 (b x)) :
    ∃ S : Schedule n, IsFeasibleOn J a b S ∧ S.s₁ x = t1 ∧ S.s₂ x = t2 := by
  subst hJ
  refine ⟨⟨fun _ => t1, fun _ => t2⟩, ?_, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    exact h0
  · intro j hj k hk hjk
    simp only [Finset.mem_singleton] at hj hk
    exact absurd (hj.trans hk.symm) hjk
  · intro j hj k hk hjk
    simp only [Finset.mem_singleton] at hj hk
    exact absurd (hj.trans hk.symm) hjk
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    subst hj
    exact hx

theorem os2_gen2 {n : ℕ} (J : Finset (Fin n)) (x y : Fin n) (hxy : x ≠ y) (hJ : J = {x, y})
    (a b : Fin n → ℝ) (t1x t1y t2x t2y : ℝ) (h0 : 0 ≤ t1x ∧ 0 ≤ t1y ∧ 0 ≤ t2x ∧ 0 ≤ t2y)
    (m1 : NoOverlap t1x (a x) t1y (a y)) (m2 : NoOverlap t2x (b x) t2y (b y))
    (jx : NoOverlap t1x (a x) t2x (b x)) (jy : NoOverlap t1y (a y) t2y (b y)) :
    ∃ S : Schedule n, IsFeasibleOn J a b S ∧ S.s₁ x = t1x ∧ S.s₁ y = t1y ∧ S.s₂ x = t2x ∧ S.s₂ y = t2y := by
  subst hJ
  obtain ⟨s1, hs1x, hs1y⟩ : ∃ s : Fin n → ℝ, s x = t1x ∧ s y = t1y :=
    ⟨fun i => if i = x then t1x else t1y, by simp, by simp [hxy.symm]⟩
  obtain ⟨s2, hs2x, hs2y⟩ : ∃ s : Fin n → ℝ, s x = t2x ∧ s y = t2y :=
    ⟨fun i => if i = x then t2x else t2y, by simp, by simp [hxy.symm]⟩
  refine ⟨⟨s1, s2⟩, ?_, hs1x, hs1y, hs2x, hs2y⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · simp only [hs1x, hs2x]; exact ⟨h0.1, h0.2.2.1⟩
    · simp only [hs1y, hs2y]; exact ⟨h0.2.1, h0.2.2.2⟩
  · intro j hj k hk hjk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
    · exact absurd rfl hjk
    · simp only [hs1x, hs1y]; exact m1
    · simp only [hs1x, hs1y]; exact os2_symm m1
    · exact absurd rfl hjk
  · intro j hj k hk hjk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
    · exact absurd rfl hjk
    · simp only [hs2x, hs2y]; exact m2
    · simp only [hs2x, hs2y]; exact os2_symm m2
    · exact absurd rfl hjk
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · simp only [hs1x, hs2x]; exact jx
    · simp only [hs1y, hs2y]; exact jy

theorem os2_gen3 {n : ℕ} (J : Finset (Fin n)) (x y z : Fin n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hJ : J = {x, y, z}) (a b : Fin n → ℝ) (t1x t1y t1z t2x t2y t2z : ℝ)
    (h0 : 0 ≤ t1x ∧ 0 ≤ t1y ∧ 0 ≤ t1z ∧ 0 ≤ t2x ∧ 0 ≤ t2y ∧ 0 ≤ t2z)
    (m1xy : NoOverlap t1x (a x) t1y (a y)) (m1xz : NoOverlap t1x (a x) t1z (a z))
    (m1yz : NoOverlap t1y (a y) t1z (a z))
    (m2xy : NoOverlap t2x (b x) t2y (b y)) (m2xz : NoOverlap t2x (b x) t2z (b z))
    (m2yz : NoOverlap t2y (b y) t2z (b z))
    (jx : NoOverlap t1x (a x) t2x (b x)) (jy : NoOverlap t1y (a y) t2y (b y))
    (jz : NoOverlap t1z (a z) t2z (b z)) :
    ∃ S : Schedule n, IsFeasibleOn J a b S ∧ S.s₁ x = t1x ∧ S.s₁ y = t1y ∧ S.s₁ z = t1z ∧
      S.s₂ x = t2x ∧ S.s₂ y = t2y ∧ S.s₂ z = t2z := by
  subst hJ
  obtain ⟨s1, hs1x, hs1y, hs1z⟩ : ∃ s : Fin n → ℝ, s x = t1x ∧ s y = t1y ∧ s z = t1z :=
    ⟨fun i => if i = x then t1x else if i = y then t1y else t1z, by simp, by simp [hxy.symm],
      by simp [hxz.symm, hyz.symm]⟩
  obtain ⟨s2, hs2x, hs2y, hs2z⟩ : ∃ s : Fin n → ℝ, s x = t2x ∧ s y = t2y ∧ s z = t2z :=
    ⟨fun i => if i = x then t2x else if i = y then t2y else t2z, by simp, by simp [hxy.symm],
      by simp [hxz.symm, hyz.symm]⟩
  refine ⟨⟨s1, s2⟩, ?_, hs1x, hs1y, hs1z, hs2x, hs2y, hs2z⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [hs1x, hs2x]; exact ⟨h0.1, h0.2.2.2.1⟩
    · simp only [hs1y, hs2y]; exact ⟨h0.2.1, h0.2.2.2.2.1⟩
    · simp only [hs1z, hs2z]; exact ⟨h0.2.2.1, h0.2.2.2.2.2⟩
  · intro j hj k hk hjk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
    · exact absurd rfl hjk
    · simp only [hs1x, hs1y]; exact m1xy
    · simp only [hs1x, hs1z]; exact m1xz
    · simp only [hs1x, hs1y]; exact os2_symm m1xy
    · exact absurd rfl hjk
    · simp only [hs1y, hs1z]; exact m1yz
    · simp only [hs1x, hs1z]; exact os2_symm m1xz
    · simp only [hs1y, hs1z]; exact os2_symm m1yz
    · exact absurd rfl hjk
  · intro j hj k hk hjk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
    rcases hj with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
    · exact absurd rfl hjk
    · simp only [hs2x, hs2y]; exact m2xy
    · simp only [hs2x, hs2z]; exact m2xz
    · simp only [hs2x, hs2y]; exact os2_symm m2xy
    · exact absurd rfl hjk
    · simp only [hs2y, hs2z]; exact m2yz
    · simp only [hs2x, hs2z]; exact os2_symm m2xz
    · simp only [hs2y, hs2z]; exact os2_symm m2yz
    · exact absurd rfl hjk
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [hs1x, hs2x]; exact jx
    · simp only [hs1y, hs2y]; exact jy
    · simp only [hs1z, hs2z]; exact jz

/-- the 3-job family with `M₁` order `x,y,z` and `M₂` order `y,z,x` -/
theorem os2_famL {n : ℕ} (J : Finset (Fin n)) (x y z : Fin n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hJ : J = {x, y, z}) (a b : Fin n → ℝ) (T : ℝ)
    (hax : 0 ≤ a x) (hay : 0 ≤ a y) (haz : 0 ≤ a z) (hbx : 0 ≤ b x) (hby : 0 ≤ b y) (hbz : 0 ≤ b z)
    (hTa : a x + a y + a z ≤ T) (hTb : b x + b y + b z ≤ T)
    (cx : a x ≤ b y + b z ∨ b y + b z + b x ≤ 0)
    (cy : a x + a y ≤ 0 ∨ b y ≤ a x)
    (cz : a x + a y + a z ≤ b y ∨ b y + b z ≤ a x + a y) :
    ∃ S : Schedule n, IsFeasibleOn J a b S ∧ ∀ j ∈ J, S.s₁ j + a j ≤ T ∧ S.s₂ j + b j ≤ T := by
  obtain ⟨S, hS, h1x, h1y, h1z, h2x, h2y, h2z⟩ := os2_gen3 J x y z hxy hxz hyz hJ a b 0 (a x) (a x + a y)
    (b y + b z) 0 (b y) ⟨le_rfl, hax, by linarith, by linarith, le_rfl, hby⟩
    (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inl (by linarith))
    (Or.inr (by linarith)) (Or.inr (by linarith)) (Or.inl (by linarith))
    (by unfold NoOverlap; rcases cx with h | h
        · left; linarith
        · right; linarith)
    (by unfold NoOverlap; rcases cy with h | h
        · left; linarith
        · right; linarith)
    (by unfold NoOverlap; rcases cz with h | h
        · left; linarith
        · right; linarith)
  refine ⟨S, hS, ?_⟩
  intro j hj
  subst hJ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · rw [h1x, h2x]; constructor <;> linarith
  · rw [h1y, h2y]; constructor <;> linarith
  · rw [h1z, h2z]; constructor <;> linarith

/-- the 3-job family with `M₁` order `x,y,z` and `M₂` order `z,x,y` -/
theorem os2_famR {n : ℕ} (J : Finset (Fin n)) (x y z : Fin n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hJ : J = {x, y, z}) (a b : Fin n → ℝ) (T : ℝ)
    (hax : 0 ≤ a x) (hay : 0 ≤ a y) (haz : 0 ≤ a z) (hbx : 0 ≤ b x) (hby : 0 ≤ b y) (hbz : 0 ≤ b z)
    (hTa : a x + a y + a z ≤ T) (hTb : b x + b y + b z ≤ T)
    (cx : a x ≤ b z ∨ b z + b x ≤ 0)
    (cy : a x + a y ≤ b z + b x ∨ b z + b x + b y ≤ a x)
    (cz : a x + a y + a z ≤ 0 ∨ b z ≤ a x + a y) :
    ∃ S : Schedule n, IsFeasibleOn J a b S ∧ ∀ j ∈ J, S.s₁ j + a j ≤ T ∧ S.s₂ j + b j ≤ T := by
  obtain ⟨S, hS, h1x, h1y, h1z, h2x, h2y, h2z⟩ := os2_gen3 J x y z hxy hxz hyz hJ a b 0 (a x) (a x + a y)
    (b z) (b z + b x) 0 ⟨le_rfl, hax, by linarith, hbz, by linarith, le_rfl⟩
    (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inl (by linarith))
    (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
    (by unfold NoOverlap; rcases cx with h | h
        · left; linarith
        · right; linarith)
    (by unfold NoOverlap; rcases cy with h | h
        · left; linarith
        · right; linarith)
    (by unfold NoOverlap; rcases cz with h | h
        · left; linarith
        · right; linarith)
  refine ⟨S, hS, ?_⟩
  intro j hj
  subst hJ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl | rfl
  · rw [h1x, h2x]; constructor <;> linarith
  · rw [h1y, h2y]; constructor <;> linarith
  · rw [h1z, h2z]; constructor <;> linarith

set_option maxHeartbeats 4000000 in
theorem os2_three_irr {n : ℕ} (J : Finset (Fin n)) (p q r : Fin n) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hqp : q ≠ p) (hrp : r ≠ p) (hrq : r ≠ q)
    (hJ : J = {p, q, r}) (a b : Fin n → ℝ) (T : ℝ)
    (hap : 0 ≤ a p) (haq : 0 ≤ a q) (har : 0 ≤ a r) (hbp : 0 ≤ b p) (hbq : 0 ≤ b q) (hbr : 0 ≤ b r)
    (hTa : a p + a q + a r ≤ T) (hTb : b p + b q + b r ≤ T)
    (hwp : a p + b p ≤ T) (hwq : a q + b q ≤ T) (hwr : a r + b r ≤ T)
    (hi1 : T < a p + b p + (a q + b q)) (hi2 : T < a p + b p + (a r + b r))
    (hi3 : T < a q + b q + (a r + b r)) :
    ∃ S : Schedule n, IsFeasibleOn J a b S ∧ ∀ j ∈ J, S.s₁ j + a j ≤ T ∧ S.s₂ j + b j ≤ T := by
  rcases le_total (a p) (b q) with h1 | h1
  · rcases le_total (a p) (b r) with h2 | h2
    · rcases le_total (a q) (b p) with h3 | h3
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J q p r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J q p r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J q r p (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J q r p (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
    · rcases le_total (a q) (b p) with h3 | h3
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J q p r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J q r p (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J q p r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J q p r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
  · rcases le_total (a p) (b r) with h2 | h2
    · rcases le_total (a q) (b p) with h3 | h3
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famR J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J r p q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J r q p (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J r p q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J r p q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
    · rcases le_total (a q) (b p) with h3 | h3
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J q r p (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famR J q r p (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inl (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
      · rcases le_total (a q) (b r) with h4 | h4
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J q p r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J q p r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p r q (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
        · rcases le_total (a r) (b p) with h5 | h5
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
          · rcases le_total (a r) (b q) with h6 | h6
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))
            · exact os2_famL J p q r (by assumption) (by assumption) (by assumption)
                      (hJ.trans (by ext i; simp only [Finset.mem_insert, Finset.mem_singleton] <;> tauto)) a b T
                      (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
                      (by linarith) (by linarith) (Or.inl (by linarith)) (Or.inr (by linarith)) (Or.inr (by linarith))

theorem os2_main {n : ℕ} (T : ℝ) : ∀ (m : ℕ) (J : Finset (Fin n)), J.card = m → ∀ (a b : Fin n → ℝ),
    (∀ j ∈ J, 0 ≤ a j ∧ 0 ≤ b j) → ∑ j ∈ J, a j ≤ T → ∑ j ∈ J, b j ≤ T →
    (∀ j ∈ J, a j + b j ≤ T) →
    ∃ S : Schedule n, IsFeasibleOn J a b S ∧ ∀ j ∈ J, S.s₁ j + a j ≤ T ∧ S.s₂ j + b j ≤ T := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro J hJc a b hnn hA hB hw
  by_cases hred : ∃ j ∈ J, ∃ k ∈ J, j ≠ k ∧ a j + b j + (a k + b k) ≤ T
  · obtain ⟨j, hj, k, hk, hjk, hjkT⟩ := hred
    -- merge the two jobs `j` and `k` into one job `j` with processing times `a j + a k`, `b j + b k`
    have hajk : 0 ≤ a k := (hnn k hk).1
    have hbjk : 0 ≤ b k := (hnn k hk).2
    have hjJ' : j ∈ J.erase k := Finset.mem_erase.2 ⟨hjk, hj⟩
    have hcard : (J.erase k).card < m := by
      rw [Finset.card_erase_of_mem hk]
      have : 0 < J.card := Finset.card_pos.2 ⟨k, hk⟩
      omega
    obtain ⟨S', hS'f, hS'c⟩ := ih (J.erase k).card hcard (J.erase k) rfl
      (fun i => a i + if i = j then a k else 0) (fun i => b i + if i = j then b k else 0)
      (by
        intro i hi
        have hiJ := (Finset.mem_erase.1 hi).2
        have h1 := hnn i hiJ
        show 0 ≤ a i + (if i = j then a k else 0) ∧ 0 ≤ b i + (if i = j then b k else 0)
        by_cases hij : i = j
        · rw [if_pos hij, if_pos hij]; constructor <;> linarith [h1.1, h1.2]
        · rw [if_neg hij, if_neg hij]; constructor <;> linarith [h1.1, h1.2])
      (by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hjJ']
        have := Finset.add_sum_erase J a hk
        linarith)
      (by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hjJ']
        have := Finset.add_sum_erase J b hk
        linarith)
      (by
        intro i hi
        have hiJ := (Finset.mem_erase.1 hi).2
        show a i + (if i = j then a k else 0) + (b i + (if i = j then b k else 0)) ≤ T
        by_cases hij : i = j
        · rw [if_pos hij, if_pos hij]; rw [hij] at *; linarith
        · rw [if_neg hij, if_neg hij]; have := hw i hiJ; linarith)
    obtain ⟨S, hS1k, hS1o, hS2k, hS2o⟩ : ∃ S : Schedule n, S.s₁ k = S'.s₁ j + a j ∧
        (∀ i, i ≠ k → S.s₁ i = S'.s₁ i) ∧ S.s₂ k = S'.s₂ j + b j ∧ (∀ i, i ≠ k → S.s₂ i = S'.s₂ i) :=
      ⟨⟨fun i => if i = k then S'.s₁ j + a j else S'.s₁ i,
        fun i => if i = k then S'.s₂ j + b j else S'.s₂ i⟩, by simp, fun i hi => by simp [hi], by simp,
        fun i hi => by simp [hi]⟩
    obtain ⟨hF0, hF1, hF2, hF3⟩ := hS'f
    -- the parent of an original job in the merged instance
    have hpiJ : ∀ i ∈ J, (if i = k then j else i) ∈ J.erase k := by
      intro i hi
      by_cases hik : i = k
      · rw [if_pos hik]; exact hjJ'
      · rw [if_neg hik]; exact Finset.mem_erase.2 ⟨hik, hi⟩
    have hb1 : ∀ i ∈ J, S'.s₁ (if i = k then j else i) ≤ S.s₁ i ∧
        S.s₁ i + a i ≤ S'.s₁ (if i = k then j else i) + (a (if i = k then j else i) +
          if (if i = k then j else i) = j then a k else 0) := by
      intro i hi
      by_cases hik : i = k
      · rw [if_pos hik, if_pos rfl, hik, hS1k]
        constructor <;> linarith [(hnn j hj).1]
      · rw [if_neg hik, hS1o i hik]
        by_cases hij : i = j
        · rw [if_pos hij]; constructor <;> linarith
        · rw [if_neg hij]; constructor <;> linarith
    have hb2 : ∀ i ∈ J, S'.s₂ (if i = k then j else i) ≤ S.s₂ i ∧
        S.s₂ i + b i ≤ S'.s₂ (if i = k then j else i) + (b (if i = k then j else i) +
          if (if i = k then j else i) = j then b k else 0) := by
      intro i hi
      by_cases hik : i = k
      · rw [if_pos hik, if_pos rfl, hik, hS2k]
        constructor <;> linarith [(hnn j hj).2]
      · rw [if_neg hik, hS2o i hik]
        by_cases hij : i = j
        · rw [if_pos hij]; constructor <;> linarith
        · rw [if_neg hij]; constructor <;> linarith
    -- two jobs with the same parent are exactly `j` and `k`
    have hsame : ∀ i₁ ∈ J, ∀ i₂ ∈ J, i₁ ≠ i₂ → (if i₁ = k then j else i₁) = (if i₂ = k then j else i₂) →
        (i₁ = k ∧ i₂ = j) ∨ (i₁ = j ∧ i₂ = k) := by
      intro i₁ h₁ i₂ h₂ hne heq
      by_cases h1k : i₁ = k
      · left
        refine ⟨h1k, ?_⟩
        have h2k : i₂ ≠ k := fun h => hne (h1k.trans h.symm)
        rw [if_pos h1k, if_neg h2k] at heq
        exact heq.symm
      · by_cases h2k : i₂ = k
        · right
          refine ⟨?_, h2k⟩
          rw [if_neg h1k, if_pos h2k] at heq
          exact heq
        · rw [if_neg h1k, if_neg h2k] at heq
          exact absurd heq hne
    refine ⟨S, ?_, ?_⟩
    swap
    · intro i hi
      have h := hS'c _ (hpiJ i hi)
      constructor
      · linarith [(hb1 i hi).2, h.1]
      · linarith [(hb2 i hi).2, h.2]
    unfold IsFeasibleOn
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      exact ⟨le_trans (hF0 _ (hpiJ i hi)).1 (hb1 i hi).1, le_trans (hF0 _ (hpiJ i hi)).2 (hb2 i hi).1⟩
    · intro p hp q hq hpq
      by_cases hpp : (if p = k then j else p) = (if q = k then j else q)
      · unfold NoOverlap
        rcases hsame p hp q hq hpq hpp with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · right
          rw [e1, e2, hS1o j hjk, hS1k]
        · left
          rw [e1, e2, hS1o j hjk, hS1k]
      · have h := hF1 _ (hpiJ p hp) _ (hpiJ q hq) hpp
        exact os2_mono h (hb1 p hp).1 (hb1 p hp).2 (hb1 q hq).1 (hb1 q hq).2
    · intro p hp q hq hpq
      by_cases hpp : (if p = k then j else p) = (if q = k then j else q)
      · unfold NoOverlap
        rcases hsame p hp q hq hpq hpp with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · right
          rw [e1, e2, hS2o j hjk, hS2k]
        · left
          rw [e1, e2, hS2o j hjk, hS2k]
      · have h := hF2 _ (hpiJ p hp) _ (hpiJ q hq) hpp
        exact os2_mono h (hb2 p hp).1 (hb2 p hp).2 (hb2 q hq).1 (hb2 q hq).2
    · intro i hi
      have h := hF3 _ (hpiJ i hi)
      exact os2_mono h (hb1 i hi).1 (hb1 i hi).2 (hb2 i hi).1 (hb2 i hi).2
  · -- no mergeable pair: at most three jobs
    have hred' : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → T < a j + b j + (a k + b k) := by
      intro j hj k hk hjk
      by_contra hc
      exact hred ⟨j, hj, k, hk, hjk, not_lt.1 hc⟩
    have hcard3 : J.card ≤ 3 := by
      by_contra hc4
      have hc4' : 3 < J.card := not_le.1 hc4
      obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
      have hc2 : 1 < ((J.erase j).erase k).card := by
        have hkJ : k ∈ J.erase j := Finset.mem_erase.2 ⟨hjk.symm, hk⟩
        rw [Finset.card_erase_of_mem hkJ, Finset.card_erase_of_mem hj]
        omega
      obtain ⟨l, hl, l', hl', hll⟩ := Finset.one_lt_card.1 hc2
      have hlJ : l ∈ J := (Finset.mem_erase.1 (Finset.mem_erase.1 hl).2).2
      have hl'J : l' ∈ J := (Finset.mem_erase.1 (Finset.mem_erase.1 hl').2).2
      have hsub : ({l, l'} : Finset (Fin n)) ⊆ (J.erase j).erase k := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hl
        · exact hl'
      have hnn' : ∀ i ∈ (J.erase j).erase k, 0 ≤ a i + b i := by
        intro i hi
        have hiJ := (Finset.mem_erase.1 (Finset.mem_erase.1 hi).2).2
        have := hnn i hiJ
        linarith [this.1, this.2]
      have hs1 : ∑ i ∈ ({l, l'} : Finset (Fin n)), (a i + b i) ≤
          ∑ i ∈ (J.erase j).erase k, (a i + b i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hnn' i hi)
      rw [Finset.sum_pair hll] at hs1
      have hkJ : k ∈ J.erase j := Finset.mem_erase.2 ⟨hjk.symm, hk⟩
      have e1 := Finset.add_sum_erase J (fun i => a i + b i) hj
      have e2 := Finset.add_sum_erase (J.erase j) (fun i => a i + b i) hkJ
      have e3 : ∑ i ∈ J, (a i + b i) = ∑ i ∈ J, a i + ∑ i ∈ J, b i := Finset.sum_add_distrib
      have h1 := hred' j hj k hk hjk
      have h2 := hred' l hlJ l' hl'J hll
      linarith
    have hJ3 : J.card = 0 ∨ J.card = 1 ∨ J.card = 2 ∨ J.card = 3 := by omega
    rcases hJ3 with h0 | h1 | h2 | h3
    · rw [Finset.card_eq_zero] at h0
      subst h0
      refine ⟨⟨fun _ => 0, fun _ => 0⟩, ?_, ?_⟩
      · unfold IsFeasibleOn
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
      · simp
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 h1
      rw [Finset.sum_singleton] at hA hB
      have hwx := hw x (by simp)
      obtain ⟨S, hS, h1x, h2x⟩ := os2_gen1 {x} x rfl a b 0 (a x) ⟨le_rfl, (hnn x (by simp)).1⟩
        (Or.inl (by linarith))
      refine ⟨S, hS, ?_⟩
      intro j hj
      simp only [Finset.mem_singleton] at hj
      subst hj
      rw [h1x, h2x]
      constructor <;> linarith [(hnn j (by simp)).2]
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 h2
      rw [Finset.sum_pair hxy] at hA hB
      have hwx := hw x (by simp)
      have hwy := hw y (by simp)
      have hax := (hnn x (by simp)).1
      have hay := (hnn y (by simp)).1
      have hbx := (hnn x (by simp)).2
      have hby := (hnn y (by simp)).2
      rcases le_total (b y) (a x) with hh | hh
      · obtain ⟨S, hS, h1x, h1y, h2x, h2y⟩ := os2_gen2 {x, y} x y hxy rfl a b 0 (a x) (a x) 0
          ⟨le_rfl, hax, hax, le_rfl⟩ (Or.inl (by linarith)) (Or.inr (by linarith))
          (Or.inl (by linarith)) (Or.inr (by linarith))
        refine ⟨S, hS, ?_⟩
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · rw [h1x, h2x]; constructor <;> linarith
        · rw [h1y, h2y]; constructor <;> linarith
      · obtain ⟨S, hS, h1x, h1y, h2x, h2y⟩ := os2_gen2 {x, y} x y hxy rfl a b 0 (b y) (b y) 0
          ⟨le_rfl, hby, hby, le_rfl⟩ (Or.inl (by linarith)) (Or.inr (by linarith))
          (Or.inl (by linarith)) (Or.inr (by linarith))
        refine ⟨S, hS, ?_⟩
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · rw [h1x, h2x]; constructor <;> linarith
        · rw [h1y, h2y]; constructor <;> linarith
    · obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.1 h3
      rw [Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_pair hqr] at hA hB
      have hwp := hw p (by simp)
      have hwq := hw q (by simp)
      have hwr := hw r (by simp)
      exact os2_three_irr {p, q, r} p q r hpq hpr hqr hpq.symm hpr.symm hqr.symm rfl a b T
        (hnn p (by simp)).1 (hnn q (by simp)).1 (hnn r (by simp)).1
        (hnn p (by simp)).2 (hnn q (by simp)).2 (hnn r (by simp)).2
        (by linarith) (by linarith) hwp hwq hwr
        (hred' p (by simp) q (by simp) hpq) (hred' p (by simp) r (by simp) hpr)
        (hred' q (by simp) r (by simp) hqr)

open SchedSurvey.O2 in
theorem solution {n : ℕ} (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hb : ∀ j, 0 ≤ b j) (T : ℝ) (hT : 0 ≤ T) :
    (∃ S : Schedule n, IsFeasible a b S ∧ CompletesBy a b S T) ↔
      (T₁ a ≤ T ∧ T₂ b ≤ T ∧ ∀ j, a j + b j ≤ T) := by
  constructor
  · rintro ⟨S, hF, hC⟩
    obtain ⟨hF0, hF1, hF2, hF3⟩ : IsFeasibleOn Finset.univ a b S := hF
    refine ⟨?_, ?_, ?_⟩
    · exact os2_sum_le S.s₁ a T hT ha (fun j => (hF0 j (Finset.mem_univ j)).1) (fun j => (hC j).1)
        (fun j k hjk => hF1 j (Finset.mem_univ j) k (Finset.mem_univ k) hjk)
    · exact os2_sum_le S.s₂ b T hT hb (fun j => (hF0 j (Finset.mem_univ j)).2) (fun j => (hC j).2)
        (fun j k hjk => hF2 j (Finset.mem_univ j) k (Finset.mem_univ k) hjk)
    · intro j
      have h := hF3 j (Finset.mem_univ j)
      have h0 := hF0 j (Finset.mem_univ j)
      have c := hC j
      unfold NoOverlap at h
      rcases h with h | h
      · linarith [h0.1, c.2]
      · linarith [h0.2, c.1]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨S, hF, hC⟩ := os2_main T n Finset.univ (by simp) a b (fun j _ => ⟨ha j, hb j⟩)
      h1 h2 (fun j _ => h3 j)
    exact ⟨S, hF, fun j => hC j (Finset.mem_univ j)⟩
