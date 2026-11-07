-- Prove2me | solution 1 for RubinsteinBargaining.PEP.pep_characterization
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-06T20:12:40.674435+00:00
-- url     : https://prove2.me/submissions/913867cb-e33e-4244-8db0-0a6602727a10

import Definitions.Def_RubinsteinBargaining_PEP_EquilibriumSets
import Definitions.Def_RubinsteinBargaining_PEP_Delta

open RubinsteinBargaining.PEP

namespace PEPCounterexample

/-- Preference induced by `w r - t` on agreements, with perpetual disagreement worst. -/
def rel (w : Partition → ℝ) : Relation := fun a b =>
  match a, b with
  | some (r, t), some (s, t') => w s - (t' : ℝ) ≤ w r - (t : ℝ)
  | some _, none => True
  | none, some _ => False
  | none, none => True

def mkPref (w : Partition → ℝ) : Preference where
  weak := rel w
  complete := by
    intro a b
    rcases a with _ | ⟨r, t⟩ <;> rcases b with _ | ⟨s, t'⟩
    · exact Or.inl trivial
    · exact Or.inr trivial
    · exact Or.inl trivial
    · exact le_total (w r - (t : ℝ)) (w s - (t' : ℝ)) |>.symm
  reflexive := by
    intro a
    rcases a with _ | ⟨r, t⟩ <;> simp [rel]
  transitive := by
    intro a b c hab hbc
    rcases a with _ | ⟨r, t⟩ <;> rcases b with _ | ⟨s, t'⟩ <;>
      rcases c with _ | ⟨u, t''⟩ <;> simp [rel] at hab hbc ⊢
    linarith

/-- Player one's (discontinuous, upper semicontinuous) valuation. -/
noncomputable def w1 (x : Partition) : ℝ := 4 * x.val + if (1/2 : ℝ) ≤ x.val then 1 else 0

def w2 (x : Partition) : ℝ := 4 * (1 - x.val)

noncomputable def p0 : Preferences where
  one := mkPref w1
  two := mkPref w2

lemma weak_some (i : Player) (r s : Partition) (t t' : ℕ) :
    weak p0 i (agreement r t) (agreement s t') ↔
      (match i with | .one => w1 | .two => w2) s - (t' : ℝ) ≤
        (match i with | .one => w1 | .two => w2) r - (t : ℝ) := by
  cases i <;> rfl

lemma weak_none (i : Player) (r : Partition) (t : ℕ) :
    weak p0 i (agreement r t) none := by
  cases i <;> trivial

lemma not_weak_none (i : Player) (r : Partition) (t : ℕ) :
    ¬ weak p0 i none (agreement r t) := by
  cases i <;> exact id

lemma w1_mono {r s : Partition} (h : s.val < r.val) : w1 s < w1 r := by
  unfold w1
  split_ifs with h1 h2 h2 <;> linarith

lemma w1_ge (x : Partition) : 4 * x.val ≤ w1 x := by
  unfold w1; split_ifs <;> linarith

lemma w1_le (x : Partition) : w1 x ≤ 4 * x.val + 1 := by
  unfold w1; split_ifs <;> linarith

lemma axioms : FullAxioms p0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- A1
    intro i r s t hlt
    refine ⟨?_, ?_⟩
    · rw [weak_some]
      cases i
      · simp only [share] at hlt; have := w1_mono hlt; linarith
      · simp only [share] at hlt; simp only [w2]; linarith
    · rw [weak_some]
      cases i
      · simp only [share] at hlt; have := w1_mono hlt; simp only; linarith
      · simp only [share] at hlt; simp only [w2]; linarith
  · -- A2
    intro i s t₁ t₂ _ hlt
    have hlt' : (t₁ : ℝ) < t₂ := by exact_mod_cast hlt
    refine ⟨⟨?_, ?_⟩, ⟨weak_none i s t₂, not_weak_none i s t₂⟩⟩
    · rw [weak_some]; cases i <;> simp only <;> linarith
    · rw [weak_some]; cases i <;> simp only <;> linarith
  · -- A3
    intro i r s t₁ t₂
    rw [weak_some, weak_some]
    push_cast
    constructor <;> intro h <;> linarith
  · -- A4
    intro i r r₀ s t₁ t₂ hr
    refine ⟨?_, fun _ => weak_none i r₀ t₁⟩
    intro hall
    have hall' := fun n => (weak_some i (r n) s t₁ t₂).1 (hall n)
    rw [weak_some]
    cases i
    · simp only at hall' ⊢
      by_cases h0 : (1/2 : ℝ) ≤ r₀.val
      · have hw : w1 r₀ = 4 * r₀.val + 1 := by unfold w1; rw [if_pos h0]
        rw [hw]
        have hlim : Filter.Tendsto (fun n => 4 * (r n : ℝ) + 1 - (t₁ : ℝ)) Filter.atTop
            (nhds (4 * (r₀ : ℝ) + 1 - (t₁ : ℝ))) := by
          exact ((hr.const_mul 4).add_const 1).sub_const _
        apply ge_of_tendsto hlim
        exact Filter.Eventually.of_forall fun n => by
          have := hall' n; have := w1_le (r n); linarith
      · push Not at h0
        have hw : w1 r₀ = 4 * r₀.val := by unfold w1; rw [if_neg (not_le.2 h0)]; ring
        rw [hw]
        have hlim : Filter.Tendsto (fun n => 4 * (r n : ℝ) - (t₁ : ℝ)) Filter.atTop
            (nhds (4 * (r₀ : ℝ) - (t₁ : ℝ))) := by
          exact (hr.const_mul 4).sub_const _
        apply ge_of_tendsto hlim
        have hev : ∀ᶠ n in Filter.atTop, (r n : ℝ) < 1/2 :=
          hr (Iio_mem_nhds h0)
        filter_upwards [hev] with n hn
        have hw' : w1 (r n) = 4 * (r n).val := by unfold w1; rw [if_neg (not_le.2 hn)]; ring
        have := hall' n
        rw [hw'] at this; linarith
    · simp only [w2] at hall' ⊢
      have hlim : Filter.Tendsto (fun n => 4 * (1 - (r n : ℝ)) - (t₁ : ℝ)) Filter.atTop
          (nhds (4 * (1 - (r₀ : ℝ)) - (t₁ : ℝ))) := by
        exact ((tendsto_const_nhds.sub hr).const_mul 4).sub_const _
      apply ge_of_tendsto hlim
      exact Filter.Eventually.of_forall fun n => hall' n
  · -- A5
    intro i r s r' s' h1 h2 _
    obtain ⟨h1a, h1b⟩ := h1
    obtain ⟨h2a, h2b⟩ := h2
    rw [weak_some] at h1a h1b h2a h2b
    cases i
    · simp only [share]
      simp only [Nat.cast_one, Nat.cast_zero] at h1a h1b h2a h2b
      -- for player one every indifference `(r,1) ~ (s,0)` has `r - s = 1/4`
      have key : ∀ r s : Partition, w1 s - 0 ≤ w1 r - 1 → w1 r - 1 ≤ w1 s - 0 →
          r.val - s.val = 1/4 := by
        intro r s ha hb
        unfold w1 at ha hb
        split_ifs at ha hb with hr hs hs <;> linarith
      have e1 := key r s h1a h1b
      have e2 := key r' s' h2a h2b
      linarith
    · simp only [share]
      simp only [w2, Nat.cast_one, Nat.cast_zero] at h1a h1b h2a h2b
      linarith

def pt (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : Partition := ⟨x, ⟨h0, h1⟩⟩

lemma quarter_mem : (1/4 : ℝ) ∈ Delta1 p0 := by
  refine ⟨0, pt (1/4) (by norm_num) (by norm_num), pt 0 (by norm_num) (by norm_num), rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show weak p0 .one (agreement _ 0) (agreement _ 1)
      rw [weak_some]; simp only [w1, pt]; norm_num
    · intro y _
      exact y.2.1
  · refine ⟨?_, ?_⟩
    · show weak p0 .two (agreement _ 0) (agreement _ 1)
      rw [weak_some]; simp only [w2, pt]; norm_num
    · intro x hx
      have hx' := (weak_some .two x _ 0 1).1 hx
      simp only [w2, pt] at hx'
      push_cast at hx'
      show x.val ≤ 1/4
      linarith

lemma one_mem : (1 : ℝ) ∈ Delta1 p0 := by
  refine ⟨3/4, pt 1 (by norm_num) (by norm_num), pt (3/4) (by norm_num) (by norm_num), rfl, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show weak p0 .one (agreement _ 0) (agreement _ 1)
      rw [weak_some]; simp only [w1, pt]; norm_num
    · intro y hy
      have hy' := (weak_some .one y _ 0 1).1 hy
      have hw : w1 (pt 1 (by norm_num) (by norm_num)) = 5 := by unfold w1 pt; norm_num
      simp only at hy'
      rw [hw] at hy'
      push_cast at hy'
      show (3/4 : ℝ) ≤ y.val
      unfold w1 at hy'
      split_ifs at hy' <;> linarith
  · refine ⟨?_, ?_⟩
    · show weak p0 .two (agreement _ 0) (agreement _ 1)
      rw [weak_some]; simp only [w2, pt]; norm_num
    · intro x _
      exact x.2.2

lemma gap_not_mem : (5/8 : ℝ) ∉ Delta1 p0 := by
  rintro ⟨y', x, y, hxy, ⟨hymem, _⟩, ⟨_, hxub⟩⟩
  simp only [Prod.mk.injEq] at hxy
  obtain ⟨hx, hy⟩ := hxy
  have hy1 := (weak_some .one y x 0 1).1 hymem
  simp only at hy1
  push_cast at hy1
  have hwx : w1 x = 7/2 := by unfold w1; rw [← hx]; norm_num
  rw [hwx] at hy1
  have hyhalf : (1/2 : ℝ) ≤ y.val := by
    unfold w1 at hy1; split_ifs at hy1 with hh
    · exact hh
    · push Not at hh
      linarith
  have hmem : pt (3/4) (by norm_num) (by norm_num) ∈
      {x' : Partition | weak p0 .two (agreement x' 0) (agreement y 1)} := by
    show weak p0 .two (agreement _ 0) (agreement _ 1)
    rw [weak_some]; simp only [w2, pt]; push_cast; linarith
  have := hxub hmem
  change (3/4 : ℝ) ≤ x.val at this
  linarith

end PEPCounterexample

open PEPCounterexample in
theorem solution : ¬ (∀ (p : Preferences) (h : FullAxioms p),
    A p = Delta1 p ∧
    (A p).Nonempty ∧
    B p = Delta2 p ∧
    (B p).Nonempty ∧
    (∃ lo hi : ℝ, lo ≤ hi ∧ A p = Set.Icc lo hi) ∧
    (∃ lo hi : ℝ, lo ≤ hi ∧ B p = Set.Icc lo hi) ∧
    ∃ e : ℝ, 0 ≤ e ∧ B p = (fun x : ℝ => x - e) '' A p) := by
  intro H
  obtain ⟨hA, -, -, -, ⟨lo, hi, -, hI⟩, -⟩ := H p0 axioms
  have h1 : (1/4 : ℝ) ∈ Set.Icc lo hi := hI ▸ hA ▸ quarter_mem
  have h2 : (1 : ℝ) ∈ Set.Icc lo hi := hI ▸ hA ▸ one_mem
  have h3 : (5/8 : ℝ) ∈ Set.Icc lo hi := ⟨by linarith [h1.1], by linarith [h2.2]⟩
  exact gap_not_mem (hA ▸ hI ▸ h3)
