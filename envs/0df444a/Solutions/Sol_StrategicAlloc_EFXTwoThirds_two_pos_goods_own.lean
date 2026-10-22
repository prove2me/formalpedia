-- Prove2me | solution 1 for StrategicAlloc.EFXTwoThirds.two_pos_goods_own
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:59:19.398655+00:00
-- url     : https://prove2.me/submissions/a0bb88e0-b68f-474d-9e54-bab9f85eefaf

import Mathlib
import Definitions.Def_StrategicAlloc_EFXTwoThirds_Setting

set_option autoImplicit false
open StrategicAlloc.EFXTwoThirds

theorem mms_le_aux {m : ℕ} (v : Fin m → ℝ) (B : ℝ)
    (hB : ∀ f : Fin m → Fin 2, ∃ j0 : Fin 2,
      ∑ g ∈ Finset.univ.filter (fun g => f g = j0), v g ≤ B) :
    LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ B := by
  classical
  unfold LittleCharity.MMS.mms
  apply ciSup_le
  intro f
  obtain ⟨j0, hj0⟩ := hB f
  refine le_trans (ciInf_le (Set.finite_range _).bddBelow j0) ?_
  convert hj0

theorem part_sum_aux {m : ℕ} (v : Fin m → ℝ) (f : Fin m → Fin 2) :
    ∑ g ∈ Finset.univ.filter (fun g => f g = 0), v g +
      ∑ g ∈ Finset.univ.filter (fun g => f g = 1), v g = ∑ g, v g := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun g => f g = 0)]
  congr 1
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext g
  have : ∀ x : Fin 2, ¬ x = 0 ↔ x = 1 := by decide
  simp [this]

theorem mms_le_half {m : ℕ} (v : Fin m → ℝ) :
    LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ (∑ g, v g) / 2 := by
  apply mms_le_aux
  intro f
  have hps := part_sum_aux v f
  by_cases h : ∑ g ∈ Finset.univ.filter (fun g => f g = 0), v g ≤ (∑ g, v g) / 2
  · exact ⟨0, h⟩
  · exact ⟨1, by linarith⟩

/-- if one good carries the whole value of `Y`, the maximin share is at most the value of the rest -/
theorem mms_le_single {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (g0 : Fin m) :
    LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ ∑ g ∈ Finset.univ.erase g0, v g := by
  apply mms_le_aux
  intro f
  by_cases h0 : f g0 = 0
  · refine ⟨1, ?_⟩
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      rw [h0] at hx
      exact absurd hx (by decide)
    · intro x _ _; exact hv x
  · refine ⟨0, ?_⟩
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      rintro rfl
      exact h0 hx
    · intro x _ _; exact hv x

/-- structural facts used for two agents -/
theorem efx2_facts {m : ℕ} (v : Fin m → ℝ) (hv : ∀ g, 0 ≤ v g) (X Y : Finset (Fin m))
    (hdisj : Disjoint X Y) (hU : X ∪ Y = Finset.univ)
    (hefx : ∀ g ∈ Y, 0 < v g → ∑ h ∈ Y.erase g, v h ≤ ∑ h ∈ X, v h) :
    (∑ g, v g = ∑ g ∈ X, v g + ∑ g ∈ Y, v g) ∧
    LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ (∑ g ∈ X, v g + ∑ g ∈ Y, v g) / 2 ∧
    (2 * ∑ g ∈ X, v g < ∑ g ∈ Y, v g →
      LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v g) 2 Finset.univ ≤ ∑ g ∈ X, v g) := by
  have hT : ∑ g, v g = ∑ g ∈ X, v g + ∑ g ∈ Y, v g := by
    rw [← Finset.sum_union hdisj, hU]
  refine ⟨hT, by rw [← hT]; exact mms_le_half v, ?_⟩
  intro hb2
  have ha : 0 ≤ ∑ g ∈ X, v g := Finset.sum_nonneg (fun g _ => hv g)
  set a := ∑ g ∈ X, v g with hadef
  set b := ∑ g ∈ Y, v g with hbdef
  obtain ⟨g0, hg0Y, hg0pos⟩ : ∃ g ∈ Y, 0 < v g := by
    by_contra hcon
    push_neg at hcon
    have : b = 0 := Finset.sum_eq_zero (fun g hg => le_antisymm (hcon g hg) (hv g))
    linarith
  have hefxg : ∀ g ∈ Y, 0 < v g → b - v g ≤ a := by
    intro g hg hpos
    have := hefx g hg hpos
    rw [Finset.sum_erase_eq_sub hg] at this
    exact this
  have hbig : ∀ g ∈ Y, 0 < v g → b < 2 * v g := by
    intro g hg hpos
    have := hefxg g hg hpos
    linarith
  have hzero : ∀ h ∈ Y, h ≠ g0 → v h = 0 := by
    intro h hh hne
    by_contra hne0
    have hpos : 0 < v h := lt_of_le_of_ne (hv h) (Ne.symm hne0)
    have h1 := hbig h hh hpos
    have h2 := hbig g0 hg0Y hg0pos
    have hpair : v h + v g0 ≤ b := by
      have : ∑ x ∈ ({h, g0} : Finset (Fin m)), v x ≤ ∑ x ∈ Y, v x :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
          (fun x _ _ => hv x)
      rwa [Finset.sum_pair hne] at this
    linarith
  have hbv : b = v g0 := by
    rw [hbdef, ← Finset.add_sum_erase Y v hg0Y]
    have : ∑ x ∈ Y.erase g0, v x = 0 :=
      Finset.sum_eq_zero (fun x hx => hzero x (Finset.mem_of_mem_erase hx) (Finset.ne_of_mem_erase hx))
    rw [this, add_zero]
  have hrest : ∑ g ∈ Finset.univ.erase g0, v g = a := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ g0), hT, hbv]; ring
  rw [← hrest]
  exact mms_le_single v hv g0

theorem efx_setup {m : ℕ} (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) (i j : Fin 2)
    (hij : i ≠ j) : Disjoint (A i) (A j) ∧ A i ∪ A j = Finset.univ := by
  refine ⟨hA.1 hij, ?_⟩
  have h2 := hA.2
  ext g
  constructor
  · intro _; exact Finset.mem_univ g
  · intro _
    have hg : g ∈ Finset.univ.biUnion A := by rw [h2]; exact Finset.mem_univ g
    rw [Finset.mem_biUnion] at hg
    obtain ⟨k, _, hk⟩ := hg
    have hk2 : ∀ a b k : Fin 2, a ≠ b → k = a ∨ k = b := by decide
    rcases hk2 i j k hij with rfl | rfl
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ hk

theorem keq2_thm {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) (hEFX : IsEFX v A)
    (i j : Fin 2) (hij : i ≠ j) (hmu : 0 < StrategicAlloc.EFXFour.mu v i)
    (hle : val v i (A i) ≤ 2 / 3 * StrategicAlloc.EFXFour.mu v i) :
    ((A j).filter (fun g => 0 < v i g)).card = 2 ∧
      val v i (A j) = 4 / 3 * StrategicAlloc.EFXFour.mu v i ∧
      ∀ g ∈ (A j).filter (fun g => 0 < v i g), v i g = 2 / 3 * StrategicAlloc.EFXFour.mu v i := by
  obtain ⟨hdisj, hU⟩ := efx_setup A hA i j hij
  have hefx : ∀ g ∈ A j, 0 < v i g → ∑ h ∈ (A j).erase g, v i h ≤ ∑ h ∈ A i, v i h :=
    fun g hg hpos => hEFX i j ⟨g, hg⟩ g hg hpos
  obtain ⟨hT, hhalf, hbig⟩ := efx2_facts (v i) (hv i) (A i) (A j) hdisj hU hefx
  have hμdef : StrategicAlloc.EFXFour.mu v i =
      LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v i g) 2 Finset.univ := rfl
  have hadef : val v i (A i) = ∑ g ∈ A i, v i g := rfl
  have hbdef : val v i (A j) = ∑ g ∈ A j, v i g := rfl
  rw [hadef] at hle
  rw [hbdef]
  set μ := StrategicAlloc.EFXFour.mu v i with hμ
  set a := ∑ g ∈ A i, v i g with hadef2
  set b := ∑ g ∈ A j, v i g with hbdef2
  have hhalf' : μ ≤ (a + b) / 2 := hhalf
  have hbig' : 2 * a < b → μ ≤ a := hbig
  have hnb : ¬ (2 * a < b) := by
    intro h
    have := hbig' h
    linarith
  push_neg at hnb
  have ha : a = 2 / 3 * μ := by linarith
  have hb : b = 4 / 3 * μ := by linarith
  refine ?_
  -- positive goods of the other bundle
  set P := (A j).filter (fun g => 0 < v i g) with hP
  have hsumP : ∑ g ∈ P, v i g = b := by
    rw [hP]
    apply Finset.sum_filter_of_ne
    intro x _ hx
    exact lt_of_le_of_ne (hv i x) (Ne.symm hx)
  have hge : ∀ g ∈ P, 2 / 3 * μ ≤ v i g := by
    intro g hg
    rw [hP, Finset.mem_filter] at hg
    have := hefx g hg.1 hg.2
    rw [Finset.sum_erase_eq_sub hg.1] at this
    linarith
  have hcard_le : P.card ≤ 2 := by
    have := Finset.card_nsmul_le_sum P (fun g => v i g) (2 / 3 * μ) hge
    rw [hsumP, nsmul_eq_mul, hb] at this
    have h3 : (P.card : ℝ) ≤ 2 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    exact_mod_cast h3
  have hcard_pos : 1 ≤ P.card := by
    by_contra hcon
    have h0 : P.card = 0 := by omega
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hsumP
    simp at hsumP
    linarith
  have hcard_ne : P.card ≠ 1 := by
    intro h1
    obtain ⟨g0, hg0⟩ := Finset.card_eq_one.mp h1
    rw [hg0, Finset.sum_singleton] at hsumP
    have hrest : ∑ g ∈ Finset.univ.erase g0, v i g = a := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ g0), hT, ← hsumP]; ring
    have this' := mms_le_single (v i) (hv i) g0
    rw [hrest] at this'
    have this : μ ≤ a := this'
    linarith
  have hcard : P.card = 2 := by omega
  obtain ⟨x, y, hxy, hPxy⟩ := Finset.card_eq_two.mp hcard
  have hx : 2 / 3 * μ ≤ v i x := hge x (by rw [hPxy]; simp)
  have hy : 2 / 3 * μ ≤ v i y := hge y (by rw [hPxy]; simp)
  rw [hPxy, Finset.sum_pair hxy] at hsumP
  refine ⟨hcard, hb, ?_⟩
  intro g hg
  rw [hPxy] at hg
  simp only [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl <;> linarith

theorem solution {m : ℕ} (v : Fin 2 → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (A : Fin 2 → Finset (Fin m)) (hA : IsAllocation A) (hEFX : IsEFX v A)
    (i : Fin 2) (hmu : 0 < StrategicAlloc.EFXFour.mu v i)
    (hle : val v i (A i) ≤ 2 / 3 * StrategicAlloc.EFXFour.mu v i) :
    2 ≤ ((A i).filter (fun g => 0 < v i g)).card := by
  -- the other agent
  obtain ⟨j, hij⟩ : ∃ j : Fin 2, i ≠ j := ⟨if i = 0 then 1 else 0, by fin_cases i <;> decide⟩
  obtain ⟨hcard, hb, hval⟩ := keq2_thm v hv A hA hEFX i j hij hmu hle
  obtain ⟨hdisj, hU⟩ := efx_setup A hA i j hij
  have hefx : ∀ g ∈ A j, 0 < v i g → ∑ h ∈ (A j).erase g, v i h ≤ ∑ h ∈ A i, v i h :=
    fun g hg hpos => hEFX i j ⟨g, hg⟩ g hg hpos
  obtain ⟨hT, hhalf, hbig⟩ := efx2_facts (v i) (hv i) (A i) (A j) hdisj hU hefx
  have hμdef : StrategicAlloc.EFXFour.mu v i =
      LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v i g) 2 Finset.univ := rfl
  have hadef : val v i (A i) = ∑ g ∈ A i, v i g := rfl
  have hbdef : val v i (A j) = ∑ g ∈ A j, v i g := rfl
  rw [hadef] at hle
  rw [hbdef] at hb
  set μ := StrategicAlloc.EFXFour.mu v i with hμ
  set a := ∑ g ∈ A i, v i g with hadef2
  set b := ∑ g ∈ A j, v i g with hbdef2
  have hhalf' : μ ≤ (a + b) / 2 := hhalf
  have ha : a = 2 / 3 * μ := by linarith
  -- positive goods
  set P := (A j).filter (fun g => 0 < v i g) with hP
  set Q := (A i).filter (fun g => 0 < v i g) with hQ
  have hsumQ : ∑ g ∈ Q, v i g = a := by
    rw [hQ]
    apply Finset.sum_filter_of_ne
    intro x _ hx
    exact lt_of_le_of_ne (hv i x) (Ne.symm hx)
  by_contra hlt
  push_neg at hlt
  have hQne : Q.card ≠ 0 := by
    intro h0
    rw [Finset.card_eq_zero] at h0
    rw [h0] at hsumQ
    simp at hsumQ
    linarith
  have hQ1 : Q.card = 1 := by omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hQ1
  obtain ⟨x, y, hxy, hPxy⟩ := Finset.card_eq_two.mp hcard
  have hvx : v i x = 2 / 3 * μ := hval x (by rw [hPxy]; simp)
  have hvy : v i y = 2 / 3 * μ := hval y (by rw [hPxy]; simp)
  have hvz : v i z = 2 / 3 * μ := by
    rw [hz, Finset.sum_singleton] at hsumQ
    rw [hsumQ, ha]
  have hxj : x ∈ A j := (Finset.mem_filter.mp (by rw [hPxy]; simp : x ∈ P)).1
  have hyj : y ∈ A j := (Finset.mem_filter.mp (by rw [hPxy]; simp : y ∈ P)).1
  have hzi : z ∈ A i := (Finset.mem_filter.mp (by rw [hz]; simp : z ∈ Q)).1
  have hzx : z ≠ x := fun h => Finset.disjoint_left.mp hdisj hzi (h ▸ hxj)
  have hzy : z ≠ y := fun h => Finset.disjoint_left.mp hdisj hzi (h ▸ hyj)
  -- every positive good is one of x, y, z
  have hpos : ∀ g, 0 < v i g → g = x ∨ g = y ∨ g = z := by
    intro g hg
    have hgU : g ∈ A i ∪ A j := by rw [hU]; exact Finset.mem_univ g
    rcases Finset.mem_union.mp hgU with h | h
    · have : g ∈ Q := Finset.mem_filter.mpr ⟨h, hg⟩
      rw [hz] at this
      right; right; simpa using this
    · have : g ∈ P := Finset.mem_filter.mpr ⟨h, hg⟩
      rw [hPxy] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      tauto
  have h3 : ∀ c1 c2 c3 : Fin 2, ∃ j0 : Fin 2, (c1 = j0 → c2 = j0 → False) ∧
      (c1 = j0 → c3 = j0 → False) ∧ (c2 = j0 → c3 = j0 → False) := by decide
  have hmms : μ ≤ 2 / 3 * μ := by
    have : LittleCharity.MMS.mms (fun S => ∑ g ∈ S, v i g) 2 Finset.univ ≤ 2 / 3 * μ := by
      apply mms_le_aux
      intro f
      obtain ⟨j0, h12, h13, h23⟩ := h3 (f x) (f y) (f z)
      refine ⟨j0, ?_⟩
      have hS : ∑ g ∈ Finset.univ.filter (fun g => f g = j0), v i g =
          ∑ g ∈ (Finset.univ.filter (fun g => f g = j0)).filter (fun g => 0 < v i g), v i g := by
        symm
        apply Finset.sum_filter_of_ne
        intro g _ hg
        exact lt_of_le_of_ne (hv i g) (Ne.symm hg)
      rw [hS]
      set S := (Finset.univ.filter (fun g => f g = j0)).filter (fun g => 0 < v i g) with hSdef
      have hSle : ∀ g ∈ S, v i g ≤ 2 / 3 * μ := by
        intro g hg
        rw [hSdef, Finset.mem_filter] at hg
        rcases hpos g hg.2 with rfl | rfl | rfl <;> linarith
      have hScard : S.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro g1 hg1 g2 hg2
        rw [hSdef, Finset.mem_filter, Finset.mem_filter] at hg1 hg2
        simp only [Finset.mem_univ, true_and] at hg1 hg2
        rcases hpos g1 hg1.2 with rfl | rfl | rfl <;> rcases hpos g2 hg2.2 with rfl | rfl | rfl <;>
          first
          | rfl
          | (exfalso; first
              | exact h12 hg1.1 hg2.1 | exact h12 hg2.1 hg1.1
              | exact h13 hg1.1 hg2.1 | exact h13 hg2.1 hg1.1
              | exact h23 hg1.1 hg2.1 | exact h23 hg2.1 hg1.1)
      calc ∑ g ∈ S, v i g ≤ S.card • (2 / 3 * μ) := Finset.sum_le_card_nsmul S _ _ hSle
        _ ≤ 2 / 3 * μ := by
          rw [nsmul_eq_mul]
          have : (S.card : ℝ) ≤ 1 := by exact_mod_cast hScard
          nlinarith
    exact this
  linarith
