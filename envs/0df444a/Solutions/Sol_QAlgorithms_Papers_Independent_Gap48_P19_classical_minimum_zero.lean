-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P19.classical_minimum_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:44:20.313796+00:00
-- url     : https://prove2.me/submissions/d9f3a476-2663-46dd-b7e7-10cf43383409

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_lawMap_sum {I J : Type} [Fintype I] [Fintype J] (p : I → ℝ) (f : I → J) (g : J → ℝ) :
    ∑ j, lawMap p f j * g j = ∑ i, p i * g (f i) := by
  simp only [lawMap, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single (f i)]
  · rw [if_pos rfl]
  · intro j _ hj; rw [if_neg (fun h => hj h.symm), zero_mul]
  · simp

theorem x8_lawMap_ge {I J : Type} [Fintype I] (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (f : I → J) (i : I) :
    p i ≤ lawMap p f (f i) := by
  unfold lawMap
  have := Finset.single_le_sum (f := fun k => if f k = f i then p k else 0)
    (fun k _ => ite_nonneg (hp k) (le_refl 0)) (Finset.mem_univ i)
  calc p i = (if f i = f i then p i else 0) := (if_pos rfl).symm
    _ ≤ _ := this

theorem x8_lawMap_nonneg {I J : Type} [Fintype I] (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (f : I → J) (j : J) :
    0 ≤ lawMap p f j := by
  unfold lawMap
  exact Finset.sum_nonneg (fun k _ => by split_ifs; exact hp k; exact le_refl 0)

theorem x8_lawMap_single {I J : Type} [Fintype I] (p : I → ℝ) (f : I → J) (i0 : I)
    (h : ∀ i, f i = f i0 → p i ≠ 0 → i = i0) : lawMap p f (f i0) = p i0 := by
  unfold lawMap
  rw [Finset.sum_eq_single i0]
  · rw [if_pos rfl]
  · intro i _ hi
    by_cases h1 : f i = f i0
    · rw [if_pos h1]; by_contra h2; exact hi (h i h1 h2)
    · rw [if_neg h1]
  · simp

theorem x8_lawMap_total {I J : Type} [Fintype I] [Fintype J] (p : I → ℝ) (f : I → J) :
    ∑ j, lawMap p f j = ∑ i, p i := by
  have := x8_lawMap_sum p f (fun _ => 1)
  simpa using this

/-- CMI in pointwise form. -/
theorem x8_cmi_eq {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (p : (A × B) × L → ℝ) :
    extensionClassicalCMI p = ∑ z, p z * (Real.log (p z) + Real.log (lawMap p Prod.snd z.2) -
      Real.log (lawMap p (fun z => (z.1.1, z.2)) (z.1.1, z.2)) -
      Real.log (lawMap p (fun z => (z.1.2, z.2)) (z.1.2, z.2))) := by
  unfold extensionClassicalCMI shannonNats
  rw [x8_lawMap_sum p (fun z => (z.1.1, z.2)) (fun j => Real.log (lawMap p (fun z => (z.1.1, z.2)) j)),
    x8_lawMap_sum p (fun z => (z.1.2, z.2)) (fun j => Real.log (lawMap p (fun z => (z.1.2, z.2)) j)),
    x8_lawMap_sum p Prod.snd (fun j => Real.log (lawMap p Prod.snd j))]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Σ_b m2(b,l) = m3(l). -/
theorem x8_m2_sum {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (p : (A × B) × L → ℝ) (l : L) :
    ∑ b, lawMap p (fun z => (z.1.2, z.2)) (b, l) = lawMap p Prod.snd l := by
  have h := x8_lawMap_sum p (fun z => (z.1.2, z.2)) (fun j => if j.2 = l then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [Fintype.sum_prod_type] at h
  have h2 : ∀ b : B, (∑ l' : L, if l' = l then lawMap p (fun z => (z.1.2, z.2)) (b, l') else 0) =
      lawMap p (fun z => (z.1.2, z.2)) (b, l) := by
    intro b
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl]
    · intro l' _ hl; rw [if_neg hl]
    · simp
  simp only [h2] at h
  rw [h]
  rfl

theorem x8_Q_sum {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (p : (A × B) × L → ℝ)
    (hp : IsLaw p) :
    ∑ z : (A × B) × L, lawMap p (fun z => (z.1.1, z.2)) (z.1.1, z.2) *
      lawMap p (fun z => (z.1.2, z.2)) (z.1.2, z.2) / lawMap p Prod.snd z.2 = 1 := by
  set m1 := lawMap p (fun z : (A × B) × L => (z.1.1, z.2))
  set m2 := lawMap p (fun z : (A × B) × L => (z.1.2, z.2))
  set m3 := lawMap p (Prod.snd : (A × B) × L → L)
  have e1 : ∑ z : (A × B) × L, m1 (z.1.1, z.2) * m2 (z.1.2, z.2) / m3 z.2 =
      ∑ j : A × L, m1 j * ((∑ b, m2 (b, j.2)) / m3 j.2) := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [e1]
  simp only [m2, x8_m2_sum]
  rw [x8_lawMap_sum p (fun z => (z.1.1, z.2)) (fun j => m3 j.2 / m3 j.2)]
  rw [← hp.2]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  dsimp only
  rcases eq_or_lt_of_le (hp.1 z) with h | h
  · rw [← h, zero_mul]
  · have : 0 < m3 z.2 := lt_of_lt_of_le h (x8_lawMap_ge p hp.1 Prod.snd z)
    rw [div_self this.ne', mul_one]

/-- classical strong subadditivity: the CMI of a law is nonnegative. -/
theorem x8_cmi_nonneg {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (p : (A × B) × L → ℝ)
    (hp : IsLaw p) : 0 ≤ extensionClassicalCMI p := by
  rw [x8_cmi_eq]
  set m1 := lawMap p (fun z : (A × B) × L => (z.1.1, z.2))
  set m2 := lawMap p (fun z : (A × B) × L => (z.1.2, z.2))
  set m3 := lawMap p (Prod.snd : (A × B) × L → L)
  have key : ∀ z, p z - m1 (z.1.1, z.2) * m2 (z.1.2, z.2) / m3 z.2 ≤
      p z * (Real.log (p z) + Real.log (m3 z.2) - Real.log (m1 (z.1.1, z.2)) -
        Real.log (m2 (z.1.2, z.2))) := by
    intro z
    have h1 := x8_lawMap_nonneg p hp.1 (fun z : (A × B) × L => (z.1.1, z.2)) (z.1.1, z.2)
    have h2 := x8_lawMap_nonneg p hp.1 (fun z : (A × B) × L => (z.1.2, z.2)) (z.1.2, z.2)
    have h3 := x8_lawMap_nonneg p hp.1 (Prod.snd : (A × B) × L → L) z.2
    rcases eq_or_lt_of_le (hp.1 z) with h | h
    · rw [← h, zero_mul, zero_sub, neg_nonpos]
      exact div_nonneg (mul_nonneg h1 h2) h3
    · have g1 : p z ≤ m1 (z.1.1, z.2) := x8_lawMap_ge p hp.1 (fun z : (A × B) × L => (z.1.1, z.2)) z
      have g2 : p z ≤ m2 (z.1.2, z.2) := x8_lawMap_ge p hp.1 (fun z : (A × B) × L => (z.1.2, z.2)) z
      have g3 : p z ≤ m3 z.2 := x8_lawMap_ge p hp.1 (Prod.snd : (A × B) × L → L) z
      set x := m1 (z.1.1, z.2); set y := m2 (z.1.2, z.2); set t := m3 z.2
      have hx : 0 < x := lt_of_lt_of_le h g1
      have hy : 0 < y := lt_of_lt_of_le h g2
      have ht : 0 < t := lt_of_lt_of_le h g3
      have hr : 0 < x * y / t / p z := by positivity
      have hl := Real.log_le_sub_one_of_pos hr
      have e : Real.log (x * y / t / p z) =
          Real.log x + Real.log y - Real.log t - Real.log (p z) := by
        rw [Real.log_div (by positivity) h.ne', Real.log_div (by positivity) ht.ne',
          Real.log_mul hx.ne' hy.ne']
      rw [e] at hl
      have : p z * (x * y / t / p z) = x * y / t := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hl h.le]
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => key z)
  rw [Finset.sum_sub_distrib, hp.2, x8_Q_sum p hp, sub_self] at hs
  exact hs

/-- CMI vanishes when all three marginals agree with p on its support. -/
theorem x8_cmi_zero_of {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (p : (A × B) × L → ℝ)
    (h : ∀ z, p z ≠ 0 →
      Real.log (p z) + Real.log (lawMap p Prod.snd z.2) -
        Real.log (lawMap p (fun z => (z.1.1, z.2)) (z.1.1, z.2)) -
        Real.log (lawMap p (fun z => (z.1.2, z.2)) (z.1.2, z.2)) = 0) :
    extensionClassicalCMI p = 0 := by
  rw [x8_cmi_eq]
  refine Finset.sum_eq_zero (fun z _ => ?_)
  by_cases hz : p z = 0
  · rw [hz, zero_mul]
  · rw [h z hz, mul_zero]

/-- the copy extension -/
def x8copy {A B : Type} [Fintype A] [Fintype B] (p : A × B → ℝ) :
    ClassicalExtension A B :=
  ⟨Fintype.card (A × B), fun z => if (Fintype.equivFin (A × B)).symm z.2 = z.1 then p z.1 else 0⟩

theorem x8_copy_valid {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A × B → ℝ) (hp : IsLaw p) : ValidClassical p (x8copy p) := by
  have key : ∀ (k : Fin (Fintype.card (A × B))) (x : A × B),
      (Fintype.equivFin (A × B)).symm k = x ↔ k = Fintype.equivFin (A × B) x := by
    intro k x; constructor
    · rintro rfl; simp
    · rintro rfl; simp
  refine ⟨Fintype.card_pos, ⟨fun z => ?_, ?_⟩, ?_⟩
  · simp only [x8copy]; split_ifs; exact hp.1 _; exact le_refl 0
  · refine Eq.trans ?_ hp.2
    change ∑ z : (A × B) × Fin (Fintype.card (A × B)),
      (if (Fintype.equivFin (A × B)).symm z.2 = z.1 then p z.1 else 0) = _
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_eq_single (Fintype.equivFin (A × B) x)]
    · rw [if_pos ((key _ _).2 rfl)]
    · intro k _ hk; rw [if_neg (fun h => hk ((key _ _).1 h))]
    · simp
  · funext x
    simp only [x8copy, lawMap]
    rw [Finset.sum_eq_single (x, Fintype.equivFin (A × B) x)]
    · rw [if_pos rfl, if_pos ((key _ _).2 rfl)]
    · intro z _ hz
      by_cases h1 : z.1 = x
      · rw [if_pos h1, if_neg]; intro h2; apply hz
        refine Prod.ext h1 ?_
        exact (key _ _).1 (h2.trans h1)
      · rw [if_neg h1]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem x8_copy_cmi {A B : Type} [Fintype A] [Fintype B] (p : A × B → ℝ) :
    extensionClassicalCMI (x8copy p).2 = 0 := by
  set P := (x8copy p).2
  have hsupp : ∀ z, P z ≠ 0 → (Fintype.equivFin (A × B)).symm z.2 = z.1 := by
    intro z hz; by_contra h; apply hz; simp only [P, x8copy]; rw [if_neg h]
  apply x8_cmi_zero_of
  intro z hz
  have uniq : ∀ z', z'.2 = z.2 → P z' ≠ 0 → z' = z := by
    intro z' h2 hz'
    have a1 := hsupp z' hz'; have a2 := hsupp z hz
    refine Prod.ext ?_ h2
    rw [← a1, ← a2, h2]
  rw [x8_lawMap_single P Prod.snd z (fun i hi hpi => uniq i hi hpi),
    x8_lawMap_single P (fun z => (z.1.1, z.2)) z
      (fun i hi hpi => uniq i (Prod.ext_iff.1 hi).2 hpi),
    x8_lawMap_single P (fun z => (z.1.2, z.2)) z
      (fun i hi hpi => uniq i (Prod.ext_iff.1 hi).2 hpi)]
  ring

/-- the unrestricted minimum is zero. -/
theorem x8_least {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (p : A × B → ℝ) (hp : IsLaw p) : IsLeast (classicalScores p) 0 := by
  refine ⟨⟨x8copy p, x8_copy_valid p hp, x8_copy_cmi p⟩, ?_⟩
  rintro r ⟨e, he, rfl⟩
  exact x8_cmi_nonneg e.2 he.2.1

theorem x8_m1_eq {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (P : (A × B) × L → ℝ) (a : A) (l : L) :
    lawMap P (fun z => (z.1.1, z.2)) (a, l) = ∑ b, P ((a, b), l) := by
  unfold lawMap
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl]
    · intro l' _ hl; rw [if_neg]; intro h; exact hl (Prod.ext_iff.1 h).2
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ ha
    refine Finset.sum_eq_zero (fun b _ => Finset.sum_eq_zero (fun l' _ => ?_))
    rw [if_neg]; intro h; exact ha (Prod.ext_iff.1 h).1
  · intro h; exact absurd (Finset.mem_univ _) h

theorem x8_m2_eq {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (P : (A × B) × L → ℝ) (b : B) (l : L) :
    lawMap P (fun z => (z.1.2, z.2)) (b, l) = ∑ a, P ((a, b), l) := by
  unfold lawMap
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single l]
    · rw [if_pos rfl]
    · intro l' _ hl; rw [if_neg]; intro h; exact hl (Prod.ext_iff.1 h).2
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b' _ hb
    refine Finset.sum_eq_zero (fun l' _ => ?_)
    rw [if_neg]; intro h; exact hb (Prod.ext_iff.1 h).1
  · intro h; exact absurd (Finset.mem_univ _) h

theorem x8_m3_eq {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (P : (A × B) × L → ℝ) (l : L) :
    lawMap P Prod.snd l = ∑ a, ∑ b, P ((a, b), l) := by
  unfold lawMap
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [Finset.sum_eq_single l]
  · rw [if_pos rfl]
  · intro l' _ hl; rw [if_neg hl]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem x8_fst_eq {A B L : Type} [Fintype A] [Fintype B] [Fintype L] (P : (A × B) × L → ℝ) (x : A × B) :
    lawMap P Prod.fst x = ∑ l, P (x, l) := by
  unfold lawMap
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
  · refine Finset.sum_congr rfl (fun l _ => ?_); rw [if_pos rfl]
  · intro x' _ hx; refine Finset.sum_eq_zero (fun l _ => ?_); rw [if_neg hx]
  · intro h; exact absurd (Finset.mem_univ _) h

end

end QAlgorithms.Papers.Independent.Gap48.P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

theorem x8_cc_cmi {A B L : Type} [Fintype A] [Fintype B] [Fintype L]
    (w : L → ℝ) (ka : L → A → ℝ) (kb : L → B → ℝ) (hka : IsKernel ka) (hkb : IsKernel kb) :
    extensionClassicalCMI (commonCause w ka kb) = 0 := by
  apply x8_cmi_zero_of
  rintro ⟨⟨a, b⟩, l⟩ hz
  simp only [x8_m1_eq, x8_m2_eq, x8_m3_eq, commonCause] at hz ⊢
  have s1 : ∑ b', ka l a * kb l b' * w l = ka l a * w l := by
    simp only [mul_comm (ka l a), mul_assoc, ← Finset.sum_mul, (hkb l).2, one_mul]
  have s2 : ∑ a', ka l a' * kb l b * w l = kb l b * w l := by
    rw [← Finset.sum_mul, ← Finset.sum_mul, (hka l).2, one_mul]
  have s3 : ∑ a', ∑ b', ka l a' * kb l b' * w l = w l := by
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [(hkb l).2, one_mul, (hka l).2, one_mul]
  rw [s1, s2, s3]
  have h1 : ka l a ≠ 0 := fun h => hz (by rw [h]; ring)
  have h2 : kb l b ≠ 0 := fun h => hz (by rw [h]; ring)
  have h3 : w l ≠ 0 := fun h => hz (by rw [h]; ring)
  rw [Real.log_mul (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2, Real.log_mul h1 h3,
    Real.log_mul h2 h3]
  ring

def x8fairF : (Bool × Bool) × Fin 1 → ℝ := fun z => fairPair z.1

def x8fair : ClassicalExtension Bool Bool := ⟨1, x8fairF⟩

theorem x8_fair_law : IsLaw fairPair := by
  refine ⟨fun z => ?_, ?_⟩
  · unfold fairPair; split_ifs <;> norm_num
  · simp [fairPair, Fintype.sum_prod_type]

theorem x8_fair_valid : ValidClassical fairPair x8fair := by
  refine ⟨Nat.one_pos, ⟨fun z => x8_fair_law.1 _, ?_⟩, ?_⟩
  · rw [← x8_fair_law.2]
    change ∑ z : (Bool × Bool) × Fin 1, x8fairF z = _
    rw [Fintype.sum_prod_type]
    simp only [x8fairF, Fin.sum_univ_one]
  · funext x
    change lawMap x8fairF Prod.fst x = _
    rw [x8_fst_eq, Fin.sum_univ_one]
    rfl

theorem x8_fair_cmi : extensionClassicalCMI x8fairF = Real.log 2 := by
  have m1 : ∀ a l, lawMap x8fairF (fun z => (z.1.1, z.2)) (a, l) = 1 / 2 := by
    intro a l; rw [x8_m1_eq]; cases a <;> simp [x8fairF, fairPair]
  have m2 : ∀ b l, lawMap x8fairF (fun z => (z.1.2, z.2)) (b, l) = 1 / 2 := by
    intro b l; rw [x8_m2_eq]; cases b <;> simp [x8fairF, fairPair]
  have m3 : ∀ l, lawMap x8fairF Prod.snd l = 1 := by
    intro l; rw [x8_m3_eq]; simp [x8fairF, fairPair]
  rw [x8_cmi_eq]
  simp only [m1, m2, m3, Real.log_one, add_zero]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [x8fairF, fairPair]

theorem x8_main {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A × B → ℝ) (hp : IsLaw p) :
    IsLeast (classicalScores p) 0 ∧
    (∀ (n : ℕ) (w : Fin n → ℝ) (ka : Fin n → A → ℝ) (kb : Fin n → B → ℝ),
      IsLaw w → IsKernel ka → IsKernel kb →
      ∀ K : Set (ClassicalExtension A B),
        (∀ e ∈ K, ValidClassical p e) → ⟨n, commonCause w ka kb⟩ ∈ K →
        IsLeast {r | ∃ e ∈ K, extensionClassicalCMI e.2 = r} 0) ∧
    (IsLaw fairPair ∧ IsLeast
      {r | ∃ e : ClassicalExtension Bool Bool,
        ValidClassical fairPair e ∧ e.1 = 1 ∧ extensionClassicalCMI e.2 = r}
      (Real.log 2) ∧ 0 < Real.log 2) := by
  refine ⟨x8_least p hp, ?_, x8_fair_law, ⟨⟨x8fair, x8_fair_valid, rfl, x8_fair_cmi⟩, ?_⟩,
    Real.log_pos one_lt_two⟩
  · intro n w ka kb hw hka hkb K hK hmem
    refine ⟨⟨_, hmem, x8_cc_cmi w ka kb hka hkb⟩, ?_⟩
    rintro r ⟨e, he, rfl⟩
    exact x8_cmi_nonneg e.2 (hK e he).2.1
  · rintro r ⟨⟨n, f⟩, hv, h1, rfl⟩
    simp only at h1
    subst h1
    have hf : f = x8fairF := by
      funext z
      have := congrFun hv.2.2 z.1
      rw [x8_fst_eq, Fin.sum_univ_one] at this
      change f (z.1, 0) = fairPair z.1 at this
      have hz : z = (z.1, 0) := Prod.ext rfl (Subsingleton.elim _ _)
      rw [hz, this]; rfl
    show Real.log 2 ≤ extensionClassicalCMI f
    rw [hf, x8_fair_cmi]

end

end QAlgorithms.Papers.Independent.Gap48.P19

open QAlgorithms.Papers.Independent.Gap48.P19 in
open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw) in
attribute [local instance] Classical.propDecidable Classical.decEq in
theorem solution {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p : A × B → ℝ) (hp : IsLaw p) :
    IsLeast (classicalScores p) 0 ∧
    (∀ (n : ℕ) (w : Fin n → ℝ) (ka : Fin n → A → ℝ) (kb : Fin n → B → ℝ),
      IsLaw w → IsKernel ka → IsKernel kb →
      ∀ K : Set (ClassicalExtension A B),
        (∀ e ∈ K, ValidClassical p e) → ⟨n, commonCause w ka kb⟩ ∈ K →
        IsLeast {r | ∃ e ∈ K, extensionClassicalCMI e.2 = r} 0) ∧
    (IsLaw fairPair ∧ IsLeast
      {r | ∃ e : ClassicalExtension Bool Bool,
        ValidClassical fairPair e ∧ e.1 = 1 ∧ extensionClassicalCMI e.2 = r}
      (Real.log 2) ∧ 0 < Real.log 2) :=
  x8_main p hp
