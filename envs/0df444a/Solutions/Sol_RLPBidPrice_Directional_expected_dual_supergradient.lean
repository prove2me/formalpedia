-- Prove2me | solution 1 for RLPBidPrice.Directional.expected_dual_supergradient
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T09:15:15.190198+00:00
-- url     : https://prove2.me/submissions/5999d780-f2c0-49eb-929b-dbf6267a5298

import Mathlib
import Definitions.Def_RLPBidPrice_Directional_Model

open MeasureTheory Matrix

namespace RLPDDAux
open RLPBidPrice.Directional

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)

lemma sum_mul_mulVec (μ : Fin m → ℝ) (y : Fin n → ℝ) :
    ∑ i, μ i * (A *ᵥ y) i = ∑ j, y j * ∑ i, μ i * A i j := by
  simp only [mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

lemma lagr_shift (z z' μ : Fin m → ℝ) (y₀ : Fin n → ℝ) :
    lagr A r z y₀ μ = lagr A r z' y₀ μ + ∑ i, μ i * (z i - z' i) := by
  simp only [lagr, dotProduct, mul_sub, Finset.sum_sub_distrib]
  ring

lemma rdot_le_lagr {z : Fin m → ℝ} {y₀ y : Fin n → ℝ} (μ' : Fin m → ℝ)
    (h1 : A *ᵥ y ≤ z) (h2 : 0 ≤ y) (h3 : y ≤ y₀) (hμ : 0 ≤ μ') :
    r ⬝ᵥ y ≤ lagr A r z y₀ μ' := by
  have hA1 : ∑ i, μ' i * (A *ᵥ y) i ≤ ∑ i, μ' i * z i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h1 i) (hμ i)
  rw [sum_mul_mulVec] at hA1
  have key : ∀ j, r j * y j ≤ y₀ j * max 0 (r j - ∑ i, μ' i * A i j)
      + y j * ∑ i, μ' i * A i j := by
    intro j
    have e1 : y j * (r j - ∑ i, μ' i * A i j) ≤ y j * max 0 (r j - ∑ i, μ' i * A i j) :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (h2 j)
    have e2 : y j * max 0 (r j - ∑ i, μ' i * A i j) ≤ y₀ j * max 0 (r j - ∑ i, μ' i * A i j) :=
      mul_le_mul_of_nonneg_right (h3 j) (le_max_left _ _)
    nlinarith
  have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => key j
  rw [Finset.sum_add_distrib] at this
  simp only [lagr, dotProduct]
  calc ∑ j, r j * y j ≤ _ := this
    _ ≤ _ := by
      have : ∑ j, y j * ∑ i, μ' i * A i j ≤ ∑ i, μ' i * z i := hA1
      linarith

lemma bddAbove_feas (z : Fin m → ℝ) (y₀ : Fin n → ℝ) :
    BddAbove {v : ℝ | ∃ y : Fin n → ℝ, A *ᵥ y ≤ z ∧ 0 ≤ y ∧ y ≤ y₀ ∧ v = r ⬝ᵥ y} :=
  ⟨lagr A r z y₀ 0, by
    rintro _ ⟨y, h1, h2, h3, rfl⟩
    exact rdot_le_lagr A r 0 h1 h2 h3 le_rfl⟩

lemma le_piValue {z : Fin m → ℝ} {y₀ y : Fin n → ℝ}
    (h1 : A *ᵥ y ≤ z) (h2 : 0 ≤ y) (h3 : y ≤ y₀) : r ⬝ᵥ y ≤ piValue A r z y₀ :=
  le_csSup (bddAbove_feas A r z y₀) ⟨y, h1, h2, h3, rfl⟩

lemma piValue_nonneg {z : Fin m → ℝ} {y₀ : Fin n → ℝ} (hz : 0 ≤ z) (hy₀ : 0 ≤ y₀) :
    0 ≤ piValue A r z y₀ := by
  have := le_piValue A r (y := 0) (z := z) (y₀ := y₀) (by simpa using hz) le_rfl hy₀
  simpa using this

lemma piValue_le_lagr {z : Fin m → ℝ} {y₀ : Fin n → ℝ} (hz : 0 ≤ z) (hy₀ : 0 ≤ y₀)
    {μ : Fin m → ℝ} (hμ : 0 ≤ μ) : piValue A r z y₀ ≤ lagr A r z y₀ μ := by
  refine csSup_le ?_ ?_
  · exact ⟨0, 0, by simpa using hz, le_rfl, hy₀, by simp⟩
  rintro _ ⟨y, h1, h2, h3, rfl⟩
  exact rdot_le_lagr A r μ h1 h2 h3 hμ

/-- Strong duality (approximate form), via Hahn–Banach separation. -/
lemma exists_lagr_lt {z : Fin m → ℝ} {y₀ : Fin n → ℝ} (hz : 0 ≤ z) (hy₀ : 0 ≤ y₀)
    {ε : ℝ} (hε : 0 < ε) : ∃ μ : Fin m → ℝ, 0 ≤ μ ∧ lagr A r z y₀ μ < piValue A r z y₀ + ε := by
  set V := piValue A r z y₀
  let Φ : (Fin n → ℝ) → (Fin m → ℝ) × ℝ := fun y => (A *ᵥ y - z, r ⬝ᵥ y - (V + ε))
  let K := Φ '' Set.Icc 0 y₀
  let C : Set ((Fin m → ℝ) × ℝ) := {p | p.1 ≤ 0 ∧ 0 ≤ p.2}
  have hΦc : Continuous Φ := by
    refine Continuous.prodMk (continuous_pi fun i => ?_) ?_ <;>
      simp only [Φ, mulVec, dotProduct, Pi.sub_apply] <;> fun_prop
  have hKc : IsCompact K := isCompact_Icc.image hΦc
  have hKv : Convex ℝ K := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s t hs ht hst
    refine ⟨s • a + t • b, convex_Icc 0 y₀ ha hb hs ht hst, ?_⟩
    obtain rfl : t = 1 - s := by linarith
    simp only [Φ]
    ext i
    · simp [mulVec_add, mulVec_smul]; ring
    · simp [dotProduct_add, dotProduct_smul]; ring
  have hCc : IsClosed C :=
    (isClosed_le continuous_fst continuous_const).inter (isClosed_le continuous_const continuous_snd)
  have hCv : Convex ℝ C := by
    rintro p ⟨hp1, hp2⟩ q ⟨hq1, hq2⟩ s t hs ht _
    refine ⟨fun i => ?_, ?_⟩
    · have h1 : p.1 i ≤ 0 := hp1 i
      have h2 : q.1 i ≤ 0 := hq1 i
      change s * p.1 i + t * q.1 i ≤ 0
      nlinarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
  have hdisj : Disjoint K C := by
    rw [Set.disjoint_left]
    rintro p ⟨y, hy, rfl⟩ ⟨h1, h2⟩
    have hle := le_piValue A r (sub_nonpos.1 h1) hy.1 hy.2
    simp only [Φ] at h2
    linarith
  obtain ⟨f, s₁, s₂, hfK, hs, hfC⟩ := geometric_hahn_banach_compact_closed hKv hKc hCv hCc hdisj
  have h0 : s₂ < 0 := by simpa using hfC 0 ⟨le_rfl, le_rfl⟩
  have hCs : ∀ p ∈ C, ∀ c : ℝ, 0 ≤ c → c • p ∈ C := by
    rintro p ⟨hp1, hp2⟩ c hc
    refine ⟨fun i => ?_, ?_⟩
    · simpa using mul_nonpos_of_nonneg_of_nonpos hc (hp1 i)
    · simpa using mul_nonneg hc hp2
  have hfCnn : ∀ p ∈ C, 0 ≤ f p := by
    intro p hp
    by_contra hneg
    push_neg at hneg
    have hc : 0 ≤ s₂ / f p := le_of_lt (div_pos_of_neg_of_neg h0 hneg)
    have := hfC _ (hCs p hp _ hc)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
    exact lt_irrefl _ this
  set c : Fin m → ℝ := fun i => f (Pi.single i 1, 0) with hc_def
  set τ : ℝ := f (0, 1) with hτ_def
  have hdecomp : ∀ a t, f (a, t) = ∑ i, a i * c i + t * τ := by
    intro a t
    have : ((a, t) : (Fin m → ℝ) × ℝ) =
        ∑ i, a i • ((Pi.single i 1 : Fin m → ℝ), (0 : ℝ)) + t • ((0 : Fin m → ℝ), (1 : ℝ)) := by
      ext i
      · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [this, map_add, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rfl
  have hcneg : ∀ i, c i ≤ 0 := by
    intro i
    have hmem : ((-(Pi.single i 1 : Fin m → ℝ)), (0 : ℝ)) ∈ C :=
      ⟨neg_nonpos.2 (Pi.single_nonneg.2 zero_le_one), le_rfl⟩
    have := hfCnn _ hmem
    have e : ((-(Pi.single i 1 : Fin m → ℝ)), (0 : ℝ)) = -((Pi.single i 1 : Fin m → ℝ), (0:ℝ)) := by
      simp
    rw [e, map_neg] at this
    simp only [c]
    linarith
  have hτ : 0 ≤ τ := hfCnn (0, 1) ⟨le_rfl, zero_le_one⟩
  have hK' : ∀ y ∈ Set.Icc 0 y₀,
      ∑ i, (A *ᵥ y - z) i * c i + (r ⬝ᵥ y - (V + ε)) * τ < 0 := by
    intro y hy
    have := hfK (Φ y) ⟨y, hy, rfl⟩
    rw [hdecomp] at this
    linarith
  have hτpos : 0 < τ := by
    rcases hτ.lt_or_eq with h | h
    · exact h
    exfalso
    have := hK' 0 ⟨le_rfl, hy₀⟩
    rw [← h] at this
    simp only [mulVec_zero, zero_sub, Pi.neg_apply, mul_zero, add_zero] at this
    have : 0 ≤ ∑ i, -z i * c i :=
      Finset.sum_nonneg fun i _ => mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (hz i)) (hcneg i)
    linarith
  set μ : Fin m → ℝ := fun i => -c i / τ with hμ_def
  have hμ0 : 0 ≤ μ := fun i => div_nonneg (neg_nonneg.2 (hcneg i)) hτ
  have hcμ : ∀ i, c i = -(μ i * τ) := fun i => by
    simp only [μ]; field_simp
  set ys : Fin n → ℝ := fun j => if 0 < r j - ∑ i, μ i * A i j then y₀ j else 0 with hys
  have hysI : ys ∈ Set.Icc 0 y₀ := by
    refine ⟨fun j => ?_, fun j => ?_⟩
    · simp only [ys]; split_ifs
      · exact hy₀ j
      · exact le_rfl
    · simp only [ys]; split_ifs
      · exact le_rfl
      · exact hy₀ j
  have hmax : ∑ j, y₀ j * max 0 (r j - ∑ i, μ i * A i j) =
      ∑ j, ys j * (r j - ∑ i, μ i * A i j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ys]
    split_ifs with h
    · rw [max_eq_right h.le]
    · push_neg at h; rw [max_eq_left h]; simp
  have e1 : ∑ i, μ i * (A *ᵥ ys - z) i = ∑ j, ys j * (∑ i, μ i * A i j) - μ ⬝ᵥ z := by
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, sum_mul_mulVec, dotProduct]
  have e2 : ∑ j, ys j * (r j - ∑ i, μ i * A i j) = r ⬝ᵥ ys - ∑ j, ys j * (∑ i, μ i * A i j) := by
    simp only [mul_sub, Finset.sum_sub_distrib, dotProduct]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hlag : lagr A r z y₀ μ = r ⬝ᵥ ys - ∑ i, μ i * (A *ᵥ ys - z) i := by
    simp only [lagr]
    rw [hmax, e1, e2]
    ring
  have := hK' ys hysI
  simp only [hcμ] at this
  refine ⟨μ, hμ0, ?_⟩
  rw [hlag]
  have e : ∑ i, (A *ᵥ ys - z) i * -(μ i * τ) = -(τ * ∑ i, μ i * (A *ᵥ ys - z) i) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [e] at this
  nlinarith

end RLPDDAux

open MeasureTheory Matrix Filter Topology

namespace RLPDDAux
open RLPBidPrice.Directional

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)

lemma R_nonneg (hr : 0 ≤ r) : 0 ≤ ⨆ j, r j := Real.iSup_nonneg fun j => hr j

lemma le_R (j : Fin n) : r j ≤ ⨆ j, r j := le_ciSup (Set.finite_range r).bddAbove j

lemma A_nonneg (hA : IsIncidence A) (i : Fin m) (j : Fin n) : 0 ≤ A i j := by
  rcases hA.1 i j with h | h <;> simp [h]

lemma lagr_clamp (hA : IsIncidence A) (hr : 0 ≤ r) {z : Fin m → ℝ} (hz : 0 ≤ z)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : 0 ≤ μ) :
    lagr A r z y₀ (fun i => min (μ i) (⨆ j, r j)) +
      ∑ i, (μ i - min (μ i) (⨆ j, r j)) * z i ≤ lagr A r z y₀ μ := by
  set R := ⨆ j, r j
  have hj : ∀ j, max 0 (r j - ∑ i, min (μ i) R * A i j) ≤ max 0 (r j - ∑ i, μ i * A i j) := by
    intro j
    by_cases hex : ∃ i, A i j = 1 ∧ R < μ i
    · obtain ⟨i, hi1, hi2⟩ := hex
      have hsum : min (μ i) R * A i j ≤ ∑ i, min (μ i) R * A i j := by
        refine Finset.single_le_sum (f := fun i => min (μ i) R * A i j) (fun k _ => ?_)
          (Finset.mem_univ i)
        exact mul_nonneg (le_min (hμ k) (R_nonneg r hr)) (A_nonneg A hA k j)
      rw [hi1, mul_one, min_eq_right hi2.le] at hsum
      have := le_R r j
      rw [max_eq_left (by linarith)]
      exact le_max_left _ _
    · push_neg at hex
      have : ∑ i, min (μ i) R * A i j = ∑ i, μ i * A i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases hA.1 i j with h | h
        · simp [h]
        · rw [min_eq_left (hex i h)]
      rw [this]
  simp only [lagr, dotProduct]
  have h1 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hj j) (hy₀ j)
  have h2 : ∑ i, min (μ i) R * z i + ∑ i, (μ i - min (μ i) R) * z i = ∑ i, μ i * z i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith

lemma clamp_mem (hr : 0 ≤ r) {μ : Fin m → ℝ} (hμ : 0 ≤ μ) :
    (fun i => min (μ i) (⨆ j, r j)) ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => ⨆ j, r j) :=
  ⟨fun i => le_min (hμ i) (R_nonneg r hr), fun i => min_le_right _ _⟩

lemma clamp_extra_nonneg {z : Fin m → ℝ} (hz : 0 ≤ z) (μ : Fin m → ℝ) (R : ℝ) :
    0 ≤ ∑ i, (μ i - min (μ i) R) * z i :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.2 (min_le_left _ _)) (hz i)

lemma continuous_lagr (z : Fin m → ℝ) (y₀ : Fin n → ℝ) :
    Continuous fun μ => lagr A r z y₀ μ := by
  unfold lagr; simp only [dotProduct]; fun_prop

lemma exists_dualOpt (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : 0 ≤ x)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) : ∃ μ, IsDualOpt A r x y₀ μ := by
  obtain ⟨μ, hμB, hmin⟩ := (isCompact_Icc (a := (0 : Fin m → ℝ)) (b := fun _ => ⨆ j, r j)).exists_isMinOn
    ⟨0, le_rfl, fun _ => R_nonneg r hr⟩ (continuous_lagr A r x y₀).continuousOn
  refine ⟨μ, hμB.1, fun μ' hμ' => ?_⟩
  have h1 := hmin (clamp_mem r hr hμ')
  have h2 := lagr_clamp A r hA hr hx hy₀ hμ'
  have h3 := clamp_extra_nonneg hx μ' (⨆ j, r j)
  simp only [Set.mem_setOf_eq] at h1
  linarith

lemma dualOpt_le_R (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) {μ : Fin m → ℝ} (hμ : IsDualOpt A r x y₀ μ) (i : Fin m) :
    μ i ≤ ⨆ j, r j := by
  by_contra hlt
  push_neg at hlt
  have hx0 : 0 ≤ x := fun i => (hx i).le
  have h2 := lagr_clamp A r hA hr hx0 hy₀ hμ.1
  have h1 := hμ.2 _ (clamp_mem r hr hμ.1).1
  have h3 : (μ i - min (μ i) (⨆ j, r j)) * x i ≤ ∑ i, (μ i - min (μ i) (⨆ j, r j)) * x i :=
    Finset.single_le_sum (f := fun i => (μ i - min (μ i) (⨆ j, r j)) * x i)
      (fun k _ => mul_nonneg (sub_nonneg.2 (min_le_left _ _)) (hx0 k)) (Finset.mem_univ i)
  rw [min_eq_right hlt.le] at h3
  have h4 : 0 < (μ i - ⨆ j, r j) * x i := mul_pos (sub_pos.2 hlt) (hx i)
  linarith

lemma lagr_dualOpt_eq {z : Fin m → ℝ} (hz : 0 ≤ z) {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀)
    {μ : Fin m → ℝ} (hμ : IsDualOpt A r z y₀ μ) : lagr A r z y₀ μ = piValue A r z y₀ := by
  refine le_antisymm ?_ (piValue_le_lagr A r hz hy₀ hμ.1)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨μ', hμ', h⟩ := exists_lagr_lt A r hz hy₀ hε
  exact lt_of_le_of_lt (hμ.2 μ' hμ') h

lemma sum_box_le {μ : Fin m → ℝ} {R : ℝ} (hμ : μ ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => R))
    (w : Fin m → ℝ) : ∑ i, μ i * w i ≤ R * ∑ i, |w i| := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 : 0 ≤ μ i := hμ.1 i
  have h1 : μ i ≤ R := hμ.2 i
  calc μ i * w i ≤ μ i * |w i| := mul_le_mul_of_nonneg_left (le_abs_self _) h0
    _ ≤ R * |w i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

lemma abs_dot_box_le {μ : Fin m → ℝ} {R : ℝ} (hμ : μ ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => R))
    (d : Fin m → ℝ) : |d ⬝ᵥ μ| ≤ R * ∑ i, |d i| := by
  rw [abs_le]
  constructor
  · have := sum_box_le hμ (-d)
    simp only [Pi.neg_apply, abs_neg, mul_neg, Finset.sum_neg_distrib] at this
    simp only [dotProduct]
    have e : ∑ i, d i * μ i = ∑ i, μ i * d i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    linarith
  · have := sum_box_le hμ d
    simp only [dotProduct]
    have e : ∑ i, d i * μ i = ∑ i, μ i * d i := Finset.sum_congr rfl fun i _ => mul_comm _ _
    linarith

/-- Lipschitz bound in the capacity vector. -/
lemma piValue_le_add (hA : IsIncidence A) (hr : 0 ≤ r) {z z' : Fin m → ℝ} (hz : 0 ≤ z)
    (hz' : 0 ≤ z') {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) :
    piValue A r z y₀ ≤ piValue A r z' y₀ + (⨆ j, r j) * ∑ i, |z i - z' i| := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨μ, hμ, h⟩ := exists_lagr_lt A r hz' hy₀ hε
  have hc := lagr_clamp A r hA hr hz' hy₀ hμ
  have hx := clamp_extra_nonneg hz' μ (⨆ j, r j)
  have hm := clamp_mem r hr hμ
  have h1 := piValue_le_lagr A r hz hy₀ hm.1
  rw [lagr_shift A r z z'] at h1
  have h2 := sum_box_le hm (fun i => z i - z' i)
  linarith

lemma piValue_le_bound (hA : IsIncidence A) (hr : 0 ≤ r) {z : Fin m → ℝ} (hz : 0 ≤ z)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) : piValue A r z y₀ ≤ (⨆ j, r j) * ∑ i, z i := by
  have h := piValue_le_lagr A r hz hy₀ (μ := fun _ => ⨆ j, r j) (fun _ => R_nonneg r hr)
  have : lagr A r z y₀ (fun _ => ⨆ j, r j) = (⨆ j, r j) * ∑ i, z i := by
    simp only [lagr, dotProduct, Finset.mul_sum]
    have : ∀ j, max 0 (r j - ∑ i, (⨆ j, r j) * A i j) = 0 := by
      intro j
      obtain ⟨i, hi⟩ := hA.2 j
      have hi1 : A i j = 1 := (hA.1 i j).resolve_left hi
      have hs : (⨆ j, r j) * A i j ≤ ∑ i, (⨆ j, r j) * A i j :=
        Finset.single_le_sum (f := fun i => (⨆ j, r j) * A i j)
          (fun k _ => mul_nonneg (R_nonneg r hr) (A_nonneg A hA k j)) (Finset.mem_univ i)
      rw [hi1, mul_one] at hs
      have := le_R r j
      exact max_eq_left (by linarith)
    simp [this]
  linarith

/-- Lipschitz bound in the demand vector. -/
lemma piValue_le_add_y (hA : IsIncidence A) (hr : 0 ≤ r) {z : Fin m → ℝ} (hz : 0 ≤ z)
    {y y' : Fin n → ℝ} (hy : 0 ≤ y) (hy' : 0 ≤ y') :
    piValue A r z y ≤ piValue A r z y' + ∑ j, r j * |y j - y' j| := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨μ, hμ, h⟩ := exists_lagr_lt A r hz hy' hε
  have h1 := piValue_le_lagr A r hz hy hμ
  have h2 : lagr A r z y μ ≤ lagr A r z y' μ + ∑ j, r j * |y j - y' j| := by
    simp only [lagr]
    have : ∑ j, y j * max 0 (r j - ∑ i, μ i * A i j) ≤
        ∑ j, y' j * max 0 (r j - ∑ i, μ i * A i j) + ∑ j, r j * |y j - y' j| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have hc : 0 ≤ ∑ i, μ i * A i j :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hμ i) (A_nonneg A hA i j)
      have hM0 : 0 ≤ max 0 (r j - ∑ i, μ i * A i j) := le_max_left _ _
      have hM1 : max 0 (r j - ∑ i, μ i * A i j) ≤ r j := max_le (hr j) (by linarith)
      have : (y j - y' j) * max 0 (r j - ∑ i, μ i * A i j) ≤ |y j - y' j| * r j :=
        calc (y j - y' j) * max 0 (r j - ∑ i, μ i * A i j)
            ≤ |y j - y' j| * max 0 (r j - ∑ i, μ i * A i j) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) hM0
          _ ≤ |y j - y' j| * r j := mul_le_mul_of_nonneg_left hM1 (abs_nonneg _)
      nlinarith
    linarith
  linarith

lemma continuous_piValue_clamp (hA : IsIncidence A) (hr : 0 ≤ r) {z : Fin m → ℝ} (hz : 0 ≤ z) :
    Continuous fun y : Fin n → ℝ => piValue A r z (fun j => max (y j) 0) := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal (∑ j, r j)) fun a b => ?_).continuous
  have ha : (0 : Fin n → ℝ) ≤ fun j => max (a j) 0 := fun j => le_max_right _ _
  have hb : (0 : Fin n → ℝ) ≤ fun j => max (b j) 0 := fun j => le_max_right _ _
  have h1 := piValue_le_add_y A r hA hr hz ha hb
  have h2 := piValue_le_add_y A r hA hr hz hb ha
  have hs : ∀ (p q : Fin n → ℝ), ∑ j, r j * |max (p j) 0 - max (q j) 0| ≤
      (∑ j, r j) * dist p q := by
    intro p q
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hr j)
    calc |max (p j) 0 - max (q j) 0| ≤ |p j - q j| := abs_max_sub_max_le_abs _ _ _
      _ = dist (p j) (q j) := (Real.dist_eq _ _).symm
      _ ≤ dist p q := dist_le_pi_dist p q j
  have h3 := hs a b
  have h4 := hs b a
  rw [dist_comm b a] at h4
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg fun j _ => hr j), Real.dist_eq, abs_le]
  constructor <;> linarith

lemma aesm_piValue {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hA : IsIncidence A)
    (hr : 0 ≤ r) {z : Fin m → ℝ} (hz : 0 ≤ z) {Y : Ω → Fin n → ℝ} (hYm : Measurable Y)
    (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω) : AEStronglyMeasurable (fun ω => piValue A r z (Y ω)) P := by
  refine ((continuous_piValue_clamp A r hA hr hz).measurable.comp hYm).aestronglyMeasurable.congr ?_
  filter_upwards [hY] with ω hω
  simp only [Function.comp]
  congr 1
  funext j
  exact max_eq_left (hω j)

lemma lagr_dir (x d μ : Fin m → ℝ) (y₀ : Fin n → ℝ) (h : ℝ) :
    lagr A r (x + h • d) y₀ μ = lagr A r x y₀ μ + h * (d ⬝ᵥ μ) := by
  rw [lagr_shift A r _ x]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, dotProduct,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

lemma eventually_nonneg {x : Fin m → ℝ} (hx : ∀ i, 0 < x i) (d : Fin m → ℝ) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 ≤ x + h • d := by
  have hopen : IsOpen {z : Fin m → ℝ | ∀ i, 0 < z i} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hcont : Continuous fun h : ℝ => x + h • d := by fun_prop
  have hmem : ∀ᶠ h in 𝓝 (0 : ℝ), x + h • d ∈ {z : Fin m → ℝ | ∀ i, 0 < z i} :=
    hcont.continuousAt.preimage_mem_nhds (by simpa using hopen.mem_nhds hx)
  exact (hmem.filter_mono nhdsWithin_le_nhds).mono fun h hh i => (hh i).le

end RLPDDAux

open MeasureTheory Matrix Filter Topology

namespace RLPDDAux
open RLPBidPrice.Directional

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)

theorem dd_pointwise (hA : IsIncidence A) (hr : 0 ≤ r) {x : Fin m → ℝ} (hx : ∀ i, 0 < x i)
    {y₀ : Fin n → ℝ} (hy₀ : 0 ≤ y₀) (d : Fin m → ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ * (piValue A r (x + h • d) y₀ - piValue A r x y₀))
      (𝓝[>] 0) (𝓝 (u A r x y₀ d)) := by
  have hx0 : 0 ≤ x := fun i => (hx i).le
  set R := ⨆ j, r j with hR
  set S := {μ | IsDualOpt A r x y₀ μ} with hS
  set B := R * ∑ i, |d i| with hB
  have hB0 : 0 ≤ B := mul_nonneg (R_nonneg r hr) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  obtain ⟨μs, hμs⟩ := exists_dualOpt A r hA hr hx0 hy₀
  have hSbox : ∀ μ ∈ S, μ ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => R) := fun μ hμ =>
    ⟨hμ.1, fun i => dualOpt_le_R A r hA hr hx hy₀ hμ i⟩
  have hne : ((fun μ : Fin m → ℝ => d ⬝ᵥ μ) '' S).Nonempty := ⟨_, μs, hμs, rfl⟩
  have hbdd : BddBelow ((fun μ : Fin m → ℝ => d ⬝ᵥ μ) '' S) := by
    refine ⟨-B, ?_⟩
    rintro _ ⟨μ, hμ, rfl⟩
    have := abs_dot_box_le (hSbox μ hμ) d
    exact (abs_le.1 this).1
  have hu : u A r x y₀ d = sInf ((fun μ : Fin m → ℝ => d ⬝ᵥ μ) '' S) := rfl
  have hev := eventually_nonneg hx d
  rw [tendsto_order]
  constructor
  · intro a ha
    set a' := (a + u A r x y₀ d) / 2 with ha'
    have haa' : a < a' := by rw [ha']; linarith
    have ha'u : a' < u A r x y₀ d := by rw [ha']; linarith
    have hδ : ∃ δ > 0, ∀ μ ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => R), d ⬝ᵥ μ ≤ a' →
        piValue A r x y₀ + δ ≤ lagr A r x y₀ μ := by
      set K := Set.Icc (0 : Fin m → ℝ) (fun _ => R) ∩ {μ | d ⬝ᵥ μ ≤ a'} with hK
      rcases K.eq_empty_or_nonempty with hKe | hKn
      · refine ⟨1, one_pos, fun μ hμ hd => ?_⟩
        have : μ ∈ K := ⟨hμ, hd⟩
        rw [hKe] at this
        exact absurd this (Set.notMem_empty _)
      · have hKc : IsCompact K := isCompact_Icc.inter_right
          (isClosed_le (show Continuous fun μ : Fin m → ℝ => d ⬝ᵥ μ by
            simp only [dotProduct]; fun_prop) continuous_const)
        obtain ⟨μK, hμK, hmin⟩ := hKc.exists_isMinOn hKn (continuous_lagr A r x y₀).continuousOn
        refine ⟨lagr A r x y₀ μK - piValue A r x y₀, ?_, fun μ hμ hd => ?_⟩
        · by_contra hle
          push_neg at hle
          have hopt : μK ∈ S := ⟨hμK.1.1, fun μ' hμ' =>
            le_trans (by linarith) (piValue_le_lagr A r hx0 hy₀ hμ')⟩
          have := csInf_le hbdd ⟨μK, hopt, rfl⟩
          rw [← hu] at this
          have := hμK.2
          simp only [Set.mem_setOf_eq] at this
          linarith
        · have := hmin ⟨hμ, hd⟩
          simp only [Set.mem_setOf_eq] at this
          linarith
    obtain ⟨δ, hδ0, hδ⟩ := hδ
    have hc : (0 : ℝ) < δ / (B + |a'| + 1) := div_pos hδ0 (by positivity)
    filter_upwards [hev, Ioo_mem_nhdsGT hc] with h hz hh
    have hh0 : 0 < h := hh.1
    have hhδ : h * (B + |a'| + 1) < δ := (lt_div_iff₀ (by positivity)).1 hh.2
    have key : piValue A r x y₀ + h * a' ≤ piValue A r (x + h • d) y₀ := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨μ, hμ0, hμ⟩ := exists_lagr_lt A r hz hy₀ hε
      have hcl := lagr_clamp A r hA hr hz hy₀ hμ0
      have hcx := clamp_extra_nonneg hz μ R
      have hm := clamp_mem r hr hμ0
      set μ'' : Fin m → ℝ := fun i => min (μ i) R
      have hshift := lagr_dir A r x d μ'' y₀ h
      have hdb := abs_dot_box_le hm d
      have hle : piValue A r x y₀ + h * a' ≤ lagr A r (x + h • d) y₀ μ'' := by
        rw [hshift]
        by_cases hd : d ⬝ᵥ μ'' ≤ a'
        · have h1 := hδ μ'' hm hd
          have h2 : -B ≤ d ⬝ᵥ μ'' := (abs_le.1 hdb).1
          have h3 : a' ≤ |a'| := le_abs_self _
          nlinarith
        · push_neg at hd
          have h1 := piValue_le_lagr A r hx0 hy₀ hm.1
          nlinarith
      linarith
    rw [lt_inv_mul_iff₀ hh0]
    nlinarith
  · intro a ha
    obtain ⟨_, ⟨μ, hμ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hne (hu ▸ ha)
    filter_upwards [hev, self_mem_nhdsWithin] with h hz hh
    have hh0 : (0 : ℝ) < h := hh
    have h1 := piValue_le_lagr A r hz hy₀ hμ.1
    rw [lagr_dir, lagr_dualOpt_eq A r hx0 hy₀ hμ] at h1
    rw [inv_mul_lt_iff₀ hh0]
    nlinarith

end RLPDDAux


open MeasureTheory Matrix Filter Topology

namespace RLPDDAux
open RLPBidPrice.Directional

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ)

lemma M1 (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : 0 ≤ x)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (i : Fin m) (h : ℝ) (hh : 0 ≤ h) :
    |piValue A r (x + h • Pi.single i 1) y₀ - piValue A r x y₀| ≤ h * ⨆ j, r j := by
  have hz : 0 ≤ x + h • Pi.single i 1 :=
    add_nonneg hx (smul_nonneg hh (Pi.single_nonneg.2 zero_le_one))
  have e1 : ∑ k, |(x + h • (Pi.single i 1 : Fin m → ℝ)) k - x k| = h := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, abs_mul,
      abs_of_nonneg hh, ← Finset.mul_sum]
    simp [Pi.single_apply, apply_ite]
  have e2 : ∑ k, |x k - (x + h • (Pi.single i 1 : Fin m → ℝ)) k| = h := by
    exact (Finset.sum_congr rfl fun k _ => abs_sub_comm _ _).trans e1
  have h1 := piValue_le_add A r hA hr hz hx hy₀
  have h2 := piValue_le_add A r hA hr hx hz hy₀
  rw [e1] at h1
  rw [e2] at h2
  rw [abs_le]
  constructor <;> linarith

lemma M2 (x : Fin m → ℝ) (hx : 0 ≤ x)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (μ : Fin m → ℝ) (hμ : IsDualOpt A r x y₀ μ)
    (z : Fin m → ℝ) (hz : 0 ≤ z) :
    piValue A r z y₀ ≤ piValue A r x y₀ + μ ⬝ᵥ (z - x) := by
  have h1 := piValue_le_lagr A r hz hy₀ hμ.1
  rw [lagr_shift A r z x, lagr_dualOpt_eq A r hx hy₀ hμ] at h1
  simpa [dotProduct, mul_sub] using h1

lemma piValue_mono {z z' : Fin m → ℝ} (hz : 0 ≤ z) (hzz : z ≤ z') {y₀ : Fin n → ℝ}
    (hy₀ : 0 ≤ y₀) : piValue A r z y₀ ≤ piValue A r z' y₀ := by
  refine csSup_le_csSup (bddAbove_feas A r z' y₀) ⟨0, 0, by simpa using hz, le_rfl, hy₀, by simp⟩ ?_
  rintro _ ⟨y, h1, h2, h3, rfl⟩
  exact ⟨y, h1.trans hzz, h2, h3, rfl⟩

lemma M4 (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) :
    superdiff A r x y₀ = {μ | IsDualOpt A r x y₀ μ} ∧
      ∀ μ ∈ superdiff A r x y₀, ∀ i, 0 ≤ μ i ∧ μ i ≤ ⨆ j, r j := by
  have hx0 : 0 ≤ x := fun i => (hx i).le
  have hEq : superdiff A r x y₀ = {μ | IsDualOpt A r x y₀ μ} := by
    ext μ
    constructor
    · intro hμ
      have hμ0 : 0 ≤ μ := by
        intro i
        have hz : 0 ≤ x + Pi.single i 1 := add_nonneg hx0 (Pi.single_nonneg.2 zero_le_one)
        have h1 := hμ _ hz
        have h2 := piValue_mono A r hx0 (le_add_of_nonneg_right (Pi.single_nonneg.2 zero_le_one))
          hy₀ (z' := x + Pi.single i 1)
        have e : μ ⬝ᵥ (x + Pi.single i 1 - x) = μ i := by simp
        rw [e] at h1
        simp only [Pi.zero_apply]
        linarith
      refine ⟨hμ0, fun μ' hμ' => ?_⟩
      refine le_trans ?_ (piValue_le_lagr A r hx0 hy₀ hμ')
      -- choose ys
      set ys : Fin n → ℝ := fun j => if 0 < r j - ∑ i, μ i * A i j then y₀ j else 0 with hys
      have hys0 : 0 ≤ ys := fun j => by
        simp only [ys]; split_ifs
        · exact hy₀ j
        · exact le_rfl
      have hysle : ys ≤ y₀ := fun j => by
        simp only [ys]; split_ifs
        · exact le_rfl
        · exact hy₀ j
      have hAz : 0 ≤ A *ᵥ ys := fun i => by
        simp only [Pi.zero_apply, mulVec, dotProduct]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (A_nonneg A hA i j) (hys0 j)
      have h1 := hμ _ hAz
      have h2 := le_piValue A r (le_refl (A *ᵥ ys)) hys0 hysle
      have hmax : ∑ j, y₀ j * max 0 (r j - ∑ i, μ i * A i j) =
          ∑ j, ys j * (r j - ∑ i, μ i * A i j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [ys]
        split_ifs with h
        · rw [max_eq_right h.le]
        · push_neg at h; rw [max_eq_left h]; simp
      have e1 : μ ⬝ᵥ (A *ᵥ ys - x) = ∑ j, ys j * (∑ i, μ i * A i j) - μ ⬝ᵥ x := by
        simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        rw [sum_mul_mulVec]
      have e2 : ∑ j, ys j * (r j - ∑ i, μ i * A i j) =
          r ⬝ᵥ ys - ∑ j, ys j * (∑ i, μ i * A i j) := by
        simp only [mul_sub, Finset.sum_sub_distrib, dotProduct]
        congr 1
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      simp only [lagr]
      rw [hmax, e2]
      rw [e1] at h1
      linarith
    · intro hμ z hz
      exact M2 A r x hx0 y₀ hy₀ μ hμ z hz
  refine ⟨hEq, fun μ hμ i => ?_⟩
  rw [hEq] at hμ
  exact ⟨hμ.1 i, dualOpt_le_R A r hA hr hx hy₀ hμ i⟩

lemma M5 (hA : IsIncidence A) (hr : 0 ≤ r) (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (y₀ : Fin n → ℝ) (hy₀ : 0 ≤ y₀) (d : Fin m → ℝ) :
    Filter.Tendsto (fun h : ℝ => h⁻¹ * (piValue A r (x + h • d) y₀ - piValue A r x y₀))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sInf ((fun μ : Fin m → ℝ => d ⬝ᵥ μ) '' superdiff A r x y₀))) := by
  rw [(M4 A r hA hr x hx y₀ hy₀).1]
  exact dd_pointwise A r hA hr hx hy₀ d

lemma M3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hA : IsIncidence A) (hr : 0 ≤ r)
    (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (μ : Ω → Fin m → ℝ) (hμm : AEStronglyMeasurable μ P)
    (hμ : ∀ᵐ ω ∂P, IsDualOpt A r x (Y ω) (μ ω))
    (z : Fin m → ℝ) (hz : 0 ≤ z) :
    JPI P A r Y z ≤ JPI P A r Y x + (∫ ω, μ ω ∂P) ⬝ᵥ (z - x) := by
  have hx0 : 0 ≤ x := fun i => (hx i).le
  have hint : ∀ z : Fin m → ℝ, 0 ≤ z → Integrable (fun ω => piValue A r z (Y ω)) P := by
    intro z hz
    refine Integrable.of_bound (aesm_piValue A r P hA hr hz hYm hY) ((⨆ j, r j) * ∑ i, z i) ?_
    filter_upwards [hY] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (piValue_nonneg A r hz hω)]
    exact piValue_le_bound A r hA hr hz hω
  have hμi : Integrable μ P := by
    refine Integrable.of_bound hμm (⨆ j, r j) ?_
    filter_upwards [hμ, hY] with ω hω hYω
    refine (pi_norm_le_iff_of_nonneg (R_nonneg r hr)).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hω.1 i)]
    exact dualOpt_le_R A r hA hr hx hYω hω i
  have hμc : ∀ i, Integrable (fun ω => μ ω i) P := fun i => hμi.eval i
  have hdot : Integrable (fun ω => μ ω ⬝ᵥ (z - x)) P := by
    simp only [dotProduct]
    exact integrable_finsetSum _ fun i _ => (hμc i).mul_const _
  have hdotint : ∫ ω, μ ω ⬝ᵥ (z - x) ∂P = (∫ ω, μ ω ∂P) ⬝ᵥ (z - x) := by
    simp only [dotProduct]
    rw [integral_finsetSum _ fun i _ => (hμc i).mul_const _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_mul_const, eval_integral hμc]
  simp only [JPI]
  rw [← hdotint, ← integral_add (hint x hx0) hdot]
  refine integral_mono_ae (hint z hz) ((hint x hx0).add hdot) ?_
  filter_upwards [hμ, hY] with ω hω hYω
  exact M2 A r x hx0 (Y ω) hYω (μ ω) hω z hz

end RLPDDAux

open RLPBidPrice.Directional in
theorem solution {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin n → ℝ) (hA : IsIncidence A) (hr : 0 ≤ r)
    (x : Fin m → ℝ) (hx : ∀ i, 0 < x i)
    (Y : Ω → Fin n → ℝ) (hYm : Measurable Y) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (μ : Ω → Fin m → ℝ) (hμm : AEStronglyMeasurable μ P)
    (hμ : ∀ᵐ ω ∂P, IsDualOpt A r x (Y ω) (μ ω))
    (z : Fin m → ℝ) (hz : 0 ≤ z) :
    JPI P A r Y z ≤ JPI P A r Y x + (∫ ω, μ ω ∂P) ⬝ᵥ (z - x) :=
  RLPDDAux.M3 A r P hA hr x hx Y hYm hY μ hμm hμ z hz
