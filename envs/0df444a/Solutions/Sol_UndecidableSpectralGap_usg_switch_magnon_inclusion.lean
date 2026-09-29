-- Prove2me | solution 1 for UndecidableSpectralGap.usg_switch_magnon_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T08:26:02.489203+00:00
-- url     : https://prove2.me/submissions/b1336ac1-74bd-4e16-ab2e-4dfe8bf36ccb

import Definitions.Def_usg_switch_entry_data
import Definitions.Def_usg_three_state_switch
set_option autoImplicit false
set_option maxHeartbeats 8000000
open UndecidableSpectralGap

namespace AgentBUSG

variable {L : ℕ}

theorem agree_eq_iff {p q : Site L} {c c' : Config L 3}
    (h : ∀ s, s ≠ p → s ≠ q → c s = c' s) :
    c = c' ↔ c p = c' p ∧ c q = c' q := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    funext s
    by_cases hp : s = p
    · subst hp; exact h1
    by_cases hq : s = q
    · subst hq; exact h2
    exact h s hp hq

theorem agree_swap_iff {p q : Site L} (hpq : p ≠ q) {c c' : Config L 3}
    (h : ∀ s, s ≠ p → s ≠ q → c s = c' s) :
    c' = c ∘ Equiv.swap p q ↔ c' p = c q ∧ c' q = c p := by
  constructor
  · rintro rfl
    simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rintro ⟨h1, h2⟩
    funext s
    by_cases hp : s = p
    · subst hp; simp [h1]
    by_cases hq : s = q
    · subst hq; simp [h2]
    simp [Equiv.swap_apply_of_ne_of_ne hp hq, h s hp hq]

theorem one_entry (p : Site L) (a : ℝ) (c c' : Config L 3) :
    embedOne p ((a : ℂ) • switchProjector) c c' =
      if c = c' then (if c p ≠ 0 then (a : ℂ) else 0) else 0 := by
  unfold embedOne
  by_cases hc : c = c'
  · subst hc; simp [switchProjector]
  · rw [if_neg hc]
    split_ifs with hag
    · have hne : c p ≠ c' p := by
        intro he; apply hc; funext s
        by_cases hs : s = p
        · subst hs; exact he
        · exact hag s hs
      simp [switchProjector, hne]
    · rfl

theorem guard_entry (e : Site L × Site L) (hne : e.1 ≠ e.2) (c c' : Config L 3) :
    embedTwo e.1 e.2 switchGuard c c' =
      if c = c' then (if switchBoundaryAt c e then (1 : ℂ) else 0) else 0 := by
  unfold embedTwo
  by_cases hc : c = c'
  · subst hc
    simp only [implies_true, if_true]
    unfold switchGuard
    by_cases hb : switchBoundaryAt c e
    · rw [if_pos hb, if_pos ⟨rfl, hb⟩]
    · rw [if_neg hb, if_neg (fun h => hb h.2)]
  · rw [if_neg hc]
    split_ifs with hag
    · have := (agree_eq_iff hag).not.mp hc
      unfold switchGuard
      rw [if_neg]
      rintro ⟨h1, -⟩
      simp only [Prod.mk.injEq] at h1
      exact this h1
    · rfl

theorem exch_entry (e : Site L × Site L) (hne : e.1 ≠ e.2) (c c' : Config L 3) :
    embedTwo e.1 e.2 switchExchange c c' =
      if c = c' then (if c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 then (1 : ℂ) else 0)
      else (if c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧ c' = c ∘ Equiv.swap e.1 e.2
        then (-1 : ℂ) else 0) := by
  unfold embedTwo
  by_cases hag : ∀ s, s ≠ e.1 → s ≠ e.2 → c s = c' s
  · rw [if_pos hag]
    simp only [agree_eq_iff hag, agree_swap_iff hne hag]
    generalize c e.1 = x1, c e.2 = x2, c' e.1 = y1, c' e.2 = y2
    fin_cases x1 <;> fin_cases x2 <;> fin_cases y1 <;> fin_cases y2 <;>
      simp [switchExchange, switchVector]
  · rw [if_neg hag]
    have h1 : c ≠ c' := by rintro rfl; exact hag (fun _ _ _ => rfl)
    rw [if_neg h1, if_neg]
    rintro ⟨-, -, -, hsw⟩
    apply hag
    intro s hs1 hs2
    rw [hsw]
    simp [Equiv.swap_apply_of_ne_of_ne hs1 hs2]

theorem lin_entry (p q : Site L) (b : ℝ) (c c' : Config L 3) :
    embedTwo p q (switchGuard + (b : ℂ) • switchExchange) c c' =
      embedTwo p q switchGuard c c' + (b : ℂ) * embedTwo p q switchExchange c c' := by
  unfold embedTwo
  split_ifs <;> simp [Matrix.add_apply, Matrix.smul_apply]

theorem row_ne {e : Site L × Site L} (he : e ∈ rowEdges L) : e.1 ≠ e.2 := by
  intro h
  simp only [rowEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [h] at he
  omega

theorem col_ne {e : Site L × Site L} (he : e ∈ colEdges L) : e.1 ≠ e.2 := by
  intro h
  simp only [colEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
  rw [h] at he
  omega

theorem sum_ite_const {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (x : ℂ) :
    (∑ i ∈ s, if P i then x else 0) = x * ((s.filter P).card : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem rate_sum (b : ℝ) (c : Config L 3) :
    ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j =
      b * (((rowEdges L).filter (fun e => c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2)).card : ℝ) := by
  unfold switchTransitionRate
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.card_filter]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hD : c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2
  · have hne : c ∘ Equiv.swap e.1 e.2 ≠ c := by
      intro h
      have := congrFun h e.1
      simp [Equiv.swap_apply_left] at this
      exact hD.2.2 this.symm
    have hiff : ∀ x : Config L 3, (c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) ↔ x = c ∘ Equiv.swap e.1 e.2 :=
      fun x => ⟨fun h => h.2.2.2, fun h => ⟨hD.1, hD.2.1, hD.2.2, h⟩⟩
    simp only [hiff]
    rw [Finset.sum_ite_eq']
    simp [hne]
    exact hD
  · have hf : ∀ x : Config L 3, ¬(c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) := fun x h => hD ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [hf, hD, if_false, Finset.sum_const_zero]

end AgentBUSG

namespace AgentBUSG
theorem entry
    (L : ℕ) (a b : ℝ) (c c' : Config L 3) :
    switchHam L a b c c' =
      if c = c' then
        ((switchPotential L a c +
          ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j : ℝ) : ℂ)
      else -((switchTransitionRate L b c c' : ℝ) : ℂ) := by
  unfold switchHam latticeHam
  simp only [Matrix.add_apply, Matrix.sum_apply]
  rw [Finset.sum_congr rfl (fun e he => by
      rw [lin_entry, guard_entry e (row_ne he), exch_entry e (row_ne he)])]
  rw [Finset.sum_congr rfl (fun e he => guard_entry (L := L) e (col_ne he) c c')]
  simp only [one_entry]
  by_cases hc : c = c'
  · subst hc
    simp only [if_true]
    rw [rate_sum]
    unfold switchPotential switchBoundaryCount switchOccupiedCount
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, sum_ite_const, sum_ite_const, sum_ite_const, sum_ite_const]
    push_cast
    ring
  · simp only [if_neg hc, Finset.sum_const_zero, add_zero, zero_add]
    rw [← Finset.mul_sum, sum_ite_const]
    unfold switchTransitionRate
    push_cast
    ring


end AgentBUSG

namespace AgentBUSG
open UndecidableSpectralGap

variable {L : ℕ}

noncomputable def S (L : ℕ) (b : ℝ) (c : Config L 3) : ℝ :=
  ∑ j ∈ Finset.univ.erase c, switchTransitionRate L b c j

theorem rate_nonneg {b : ℝ} (hb : 0 ≤ b) (c j : Config L 3) :
    0 ≤ switchTransitionRate L b c j := by
  unfold switchTransitionRate; positivity

theorem S_nonneg {b : ℝ} (hb : 0 ≤ b) (c : Config L 3) : 0 ≤ S L b c :=
  Finset.sum_nonneg fun j _ => rate_nonneg hb c j

theorem H_diag (a b : ℝ) (c : Config L 3) :
    switchHam L a b c c = ((switchPotential L a c + S L b c : ℝ) : ℂ) := by
  rw [entry, if_pos rfl]; rfl

theorem H_off (a b : ℝ) {c j : Config L 3} (h : c ≠ j) :
    switchHam L a b c j = -((switchTransitionRate L b c j : ℝ) : ℂ) := by
  rw [entry, if_neg h]

theorem rowsum {a b : ℝ} (hb : 0 ≤ b) (c : Config L 3) :
    ∑ j ∈ Finset.univ.erase c, ‖switchHam L a b c j‖ = S L b c := by
  unfold S
  apply Finset.sum_congr rfl
  intro j hj
  rw [H_off a b (Finset.ne_of_mem_erase hj).symm, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (rate_nonneg hb c j)]

theorem eig_of_mem {A : Matrix (Config L 3) (Config L 3) ℂ} {μ : ℝ} (h : μ ∈ specReal A) :
    Module.End.HasEigenvalue (Matrix.toLin' A) (μ : ℂ) := by
  rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
  exact h

theorem mem_of_eig {A : Matrix (Config L 3) (Config L 3) ℂ} {μ : ℝ} (v : Config L 3 → ℂ)
    (hv : v ≠ 0) (h : A.mulVec v = (μ : ℂ) • v) : μ ∈ specReal A := by
  show (μ : ℂ) ∈ spectrum ℂ A
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
  refine ⟨?_, hv⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact h

/-- Gershgorin, specialised: every real eigenvalue is at least the potential of some config,
and lies in the disc of that config. -/
theorem gersh {a b : ℝ} (hb : 0 ≤ b) {μ : ℝ} (h : μ ∈ specReal (switchHam L a b)) :
    ∃ k : Config L 3, |μ - (switchPotential L a k + S L b k)| ≤ S L b k := by
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball (eig_of_mem h)
  refine ⟨k, ?_⟩
  rw [Metric.mem_closedBall, rowsum hb, H_diag, dist_eq_norm, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hk
  exact hk

theorem pot_le {a b : ℝ} (hb : 0 ≤ b) {μ : ℝ} (h : μ ∈ specReal (switchHam L a b)) :
    ∃ k : Config L 3, switchPotential L a k ≤ μ ∧
      |μ - (switchPotential L a k + S L b k)| ≤ S L b k := by
  obtain ⟨k, hk⟩ := gersh hb h
  exact ⟨k, by have := (abs_le.mp hk).1; linarith, hk⟩

def vac (L : ℕ) : Config L 3 := fun _ => 0
def ones (L : ℕ) : Config L 3 := fun _ => 1

theorem rate_vac (b : ℝ) (j : Config L 3) : switchTransitionRate L b (vac L) j = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h; exact h.1 rfl

theorem S_vac (b : ℝ) : S L b (vac L) = 0 := by
  unfold S; simp [rate_vac]

theorem rate_to_vac (b : ℝ) (c : Config L 3) : switchTransitionRate L b c (vac L) = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h
  have := congrFun h.2.2.2 e.2
  simp [vac, Equiv.swap_apply_right] at this
  exact h.1 this.symm

theorem rate_ones (b : ℝ) (j : Config L 3) : switchTransitionRate L b (ones L) j = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h; exact h.2.2.1 rfl

theorem rate_to_ones (b : ℝ) (c : Config L 3) : switchTransitionRate L b c (ones L) = 0 := by
  unfold switchTransitionRate
  rw [Finset.card_eq_zero.mpr]; · simp
  rw [Finset.filter_eq_empty_iff]
  intro e _ h
  have h1 := congrFun h.2.2.2 e.1
  have h2 := congrFun h.2.2.2 e.2
  simp [ones, Equiv.swap_apply_right, Equiv.swap_apply_left] at h1 h2
  exact h.2.2.1 (h2.symm.trans h1)

theorem pot_vac (a : ℝ) : switchPotential L a (vac L) = 0 := by
  unfold switchPotential switchOccupiedCount switchBoundaryCount switchBoundaryAt
  simp [vac]

theorem pot_ones (a : ℝ) : switchPotential L a (ones L) = a * (L : ℝ) ^ 2 := by
  unfold switchPotential switchOccupiedCount switchBoundaryCount switchBoundaryAt
  simp [ones, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

theorem mulVec_single (A : Matrix (Config L 3) (Config L 3) ℂ) (c0 : Config L 3) :
    A.mulVec (Pi.single c0 1) = fun c => A c c0 := by
  ext c
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem H_vac_col (a b : ℝ) (c : Config L 3) : switchHam L a b c (vac L) = 0 := by
  by_cases h : c = vac L
  · subst h; rw [H_diag, pot_vac, S_vac]; simp
  · rw [H_off a b h, rate_to_vac]; simp

theorem H_ones_col (a b : ℝ) (c : Config L 3) :
    switchHam L a b c (ones L) = if c = ones L then ((a * (L : ℝ) ^ 2 : ℝ) : ℂ) else 0 := by
  by_cases h : c = ones L
  · subst h; rw [H_diag, pot_ones, if_pos rfl]; unfold S; simp [rate_ones]
  · rw [H_off a b h, rate_to_ones, if_neg h]; simp

theorem zero_mem (a b : ℝ) : (0 : ℝ) ∈ specReal (switchHam L a b) := by
  refine mem_of_eig (Pi.single (vac L) 1) (by simp) ?_
  rw [mulVec_single]; ext c; simp [H_vac_col]

theorem aL_mem (a b : ℝ) : a * (L : ℝ) ^ 2 ∈ specReal (switchHam L a b) := by
  refine mem_of_eig (Pi.single (ones L) 1) (by simp) ?_
  rw [mulVec_single]; ext c
  rw [H_ones_col]
  by_cases h : c = ones L
  · subst h; simp
  · simp [h, Pi.single_apply]

theorem occ_le (c : Config L 3) : (switchOccupiedCount L c : ℝ) ≤ (L : ℝ) ^ 2 := by
  unfold switchOccupiedCount
  have := Finset.card_filter_le (Finset.univ : Finset (Site L)) (fun p => c p ≠ 0)
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at this
  have : ((Finset.univ.filter fun p : Site L => c p ≠ 0).card : ℝ) ≤ ((L * L : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at this; nlinarith

theorem pot_ge_min (a : ℝ) (c : Config L 3) :
    min 0 (a * (L : ℝ) ^ 2) ≤ switchPotential L a c := by
  unfold switchPotential
  have h0 : (0 : ℝ) ≤ (switchOccupiedCount L c : ℝ) := by positivity
  have h1 := occ_le c
  have h2 : (0 : ℝ) ≤ (switchBoundaryCount L c : ℝ) := by positivity
  rcases le_total 0 a with ha | ha
  · have : 0 ≤ a * (switchOccupiedCount L c : ℝ) := mul_nonneg ha h0
    have := min_le_left 0 (a * (L : ℝ) ^ 2); linarith
  · have : a * (L : ℝ) ^ 2 ≤ a * (switchOccupiedCount L c : ℝ) :=
      mul_le_mul_of_nonpos_left h1 ha
    have := min_le_right 0 (a * (L : ℝ) ^ 2); linarith

theorem no_bdry_const (k : Config L 3) (hL : 0 < L)
    (hrow : ∀ e ∈ rowEdges L, ¬ switchBoundaryAt k e)
    (hcol : ∀ e ∈ colEdges L, ¬ switchBoundaryAt k e) :
    ∀ s : Site L, (k s = 0 ↔ k (⟨0, hL⟩, ⟨0, hL⟩) = 0) := by
  have edge : ∀ e : Site L × Site L, ¬ switchBoundaryAt k e → (k e.1 = 0 ↔ k e.2 = 0) := by
    intro e he; unfold switchBoundaryAt at he; tauto
  have hr : ∀ (i : Fin L) (j : ℕ) (hj : j < L), (k (i, ⟨j, hj⟩) = 0 ↔ k (i, ⟨0, hL⟩) = 0) := by
    intro i j
    induction j with
    | zero => intro _; exact Iff.rfl
    | succ j ih =>
      intro hj
      have hm : ((i, ⟨j, by omega⟩), (i, ⟨j + 1, hj⟩)) ∈ rowEdges L := by
        simp [rowEdges]
      exact (edge _ (hrow _ hm)).symm.trans (ih (by omega))
  have hc : ∀ (i : ℕ) (hi : i < L), (k (⟨i, hi⟩, ⟨0, hL⟩) = 0 ↔ k (⟨0, hL⟩, ⟨0, hL⟩) = 0) := by
    intro i
    induction i with
    | zero => intro _; exact Iff.rfl
    | succ i ih =>
      intro hi
      have hm : ((⟨i, by omega⟩, ⟨0, hL⟩), (⟨i + 1, hi⟩, ⟨0, hL⟩)) ∈ colEdges L := by
        simp [colEdges]
      exact (edge _ (hcol _ hm)).symm.trans (ih (by omega))
  rintro ⟨i, j⟩
  exact (hr i j.1 j.2).trans (hc i.1 i.2)

theorem pot_ge_one {a : ℝ} (ha : 0 < a) (hL : 0 < L) (haL : 1 ≤ a * (L : ℝ) ^ 2)
    (k : Config L 3) (hk : k ≠ vac L) : 1 ≤ switchPotential L a k := by
  unfold switchPotential
  have h0 : (0 : ℝ) ≤ (switchOccupiedCount L k : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (switchBoundaryCount L k : ℝ) := by positivity
  by_cases hall : ∀ s, k s ≠ 0
  · have : switchOccupiedCount L k = L * L := by
      unfold switchOccupiedCount
      rw [Finset.filter_true_of_mem (fun s _ => hall s)]
      simp [Finset.card_univ]
    rw [this]; push_cast
    nlinarith
  · push_neg at hall
    obtain ⟨q, hq⟩ := hall
    obtain ⟨p, hp⟩ : ∃ p, k p ≠ 0 := by
      by_contra h; push_neg at h; exact hk (funext h)
    have hb : 1 ≤ switchBoundaryCount L k := by
      by_contra hcon
      have hz : switchBoundaryCount L k = 0 := by omega
      unfold switchBoundaryCount at hz
      have h1 : ((rowEdges L).filter (switchBoundaryAt k)).card = 0 := by omega
      have h2' : ((colEdges L).filter (switchBoundaryAt k)).card = 0 := by omega
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1 h2'
      have hc := no_bdry_const k hL h1 h2'
      exact hp ((hc p).mpr ((hc q).mp hq))
    have : (1 : ℝ) ≤ (switchBoundaryCount L k : ℝ) := by exact_mod_cast hb
    have : 0 ≤ a * (switchOccupiedCount L k : ℝ) := mul_nonneg ha.le h0
    linarith

theorem Hvac_mulVec (a b : ℝ) :
    (switchHam L a b).mulVec (Pi.single (vac L) 1) = 0 := by
  rw [mulVec_single]; ext c; simp [H_vac_col]

theorem eigenspace_zero {a b : ℝ} (hb : 0 ≤ b) (ha : 0 < a) (hL : 0 < L)
    (haL : 1 ≤ a * (L : ℝ) ^ 2) :
    Module.End.eigenspace (Matrix.toLin' (switchHam L a b)) 0 =
      Submodule.span ℂ {(Pi.single (vac L) 1 : Config L 3 → ℂ)} := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, zero_smul] at hv
    set w := v - v (vac L) • (Pi.single (vac L) 1 : Config L 3 → ℂ) with hw
    have hHw : (switchHam L a b).mulVec w = 0 := by
      rw [hw, Matrix.mulVec_sub, Matrix.mulVec_smul, Hvac_mulVec, hv]; simp
    have hwv : w (vac L) = 0 := by simp [hw]
    let H' : Matrix (Config L 3) (Config L 3) ℂ :=
      switchHam L a b + Matrix.of (fun k j => if k = vac L ∧ j = vac L then 1 else 0)
    have hH'w : H'.mulVec w = 0 := by
      simp only [H', Matrix.add_mulVec, hHw, zero_add]
      ext k
      by_cases hk : k = vac L
      · subst hk; simp [Matrix.mulVec, dotProduct, hwv]
      · simp [Matrix.mulVec, dotProduct, hk]
    have hdet : H'.det ≠ 0 := by
      apply det_ne_zero_of_sum_row_lt_diag
      intro k
      have hsum : ∑ j ∈ Finset.univ.erase k, ‖H' k j‖ = S L b k := by
        rw [← rowsum (a := a) hb k]
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.ne_of_mem_erase hj
        simp only [H', Matrix.add_apply, Matrix.of_apply]
        rw [if_neg (fun h => hjk (h.2.trans h.1.symm)), add_zero]
      rw [hsum]
      simp only [H', Matrix.add_apply, Matrix.of_apply]
      by_cases hk : k = vac L
      · subst hk
        rw [S_vac, if_pos ⟨rfl, rfl⟩, H_diag, pot_vac, S_vac]; simp
      · rw [if_neg (fun h => hk h.1), add_zero, H_diag, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (add_nonneg (by linarith [pot_ge_one ha hL haL k hk]) (S_nonneg hb k))]
        linarith [pot_ge_one ha hL haL k hk]
    have hw0 : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hH'w
    rw [Submodule.mem_span_singleton]
    refine ⟨v (vac L), ?_⟩
    rw [hw, sub_eq_zero] at hw0
    exact hw0.symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show _ ∈ Module.End.eigenspace _ _
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Hvac_mulVec, zero_smul]

end AgentBUSG



set_option maxHeartbeats 8000000
open UndecidableSpectralGap

namespace AgentBUSG

variable {L : ℕ}

theorem Hv_apply (a b : ℝ) (v : Config L 3 → ℂ) (c : Config L 3) :
    ((switchHam L a b).mulVec v) c =
      ((switchPotential L a c + S L b c : ℝ) : ℂ) * v c -
        (b : ℂ) * ∑ e ∈ (rowEdges L).filter (fun e => c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2),
          v (c ∘ Equiv.swap e.1 e.2) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), H_diag, sub_eq_add_neg]
  congr 1
  rw [Finset.sum_congr rfl (fun j hj => by rw [H_off a b (Finset.ne_of_mem_erase hj).symm])]
  unfold switchTransitionRate
  simp only [Finset.card_filter]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hD : c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2
  · have hne : c ∘ Equiv.swap e.1 e.2 ≠ c := by
      intro h
      have := congrFun h e.1
      simp [Equiv.swap_apply_left] at this
      exact hD.2.2 this.symm
    rw [if_pos hD]
    have hiff : ∀ x : Config L 3, (c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) ↔ x = c ∘ Equiv.swap e.1 e.2 :=
      fun x => ⟨fun h => h.2.2.2, fun h => ⟨hD.1, hD.2.1, hD.2.2, h⟩⟩
    simp only [hiff]
    rw [Finset.sum_eq_single_of_mem (c ∘ Equiv.swap e.1 e.2) (by simp [hne])]
    · simp
    · intro x _ hx; simp [hx]
  · have hf : ∀ x : Config L 3, ¬(c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2 ∧
        x = c ∘ Equiv.swap e.1 e.2) := fun x h => hD ⟨h.1, h.2.1, h.2.2.1⟩
    rw [if_neg hD]
    simp [hf]

def pat (m : Fin L → Fin L) : Config L 3 := fun p => if p.2 = m p.1 then 2 else 1

theorem pat_ne_zero (m : Fin L → Fin L) (p : Site L) : pat m p ≠ 0 := by
  unfold pat; split_ifs <;> decide

theorem pat_inj {m m' : Fin L → Fin L} (h : pat m = pat m') : m = m' := by
  funext r
  have := congrFun h (r, m r)
  simp only [pat, if_true] at this
  by_contra hne
  rw [if_neg hne] at this
  exact absurd this (by decide)

theorem pot_pat (a : ℝ) (m : Fin L → Fin L) :
    switchPotential L a (pat m) = a * (L : ℝ) ^ 2 := by
  unfold switchPotential switchOccupiedCount switchBoundaryCount switchBoundaryAt
  simp [pat_ne_zero, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]

/-- Moving the magnon of row `r` to column `j`. -/
theorem pat_swap (m : Fin L → Fin L) (r j : Fin L) (hj : j ≠ m r) :
    pat m ∘ Equiv.swap (r, m r) (r, j) = pat (Function.update m r j) := by
  funext p
  obtain ⟨p1, p2⟩ := p
  simp only [Function.comp_apply]
  by_cases h1 : (p1, p2) = (r, m r)
  · rw [h1, Equiv.swap_apply_left]
    simp [pat, hj, Ne.symm hj]
  by_cases h2 : (p1, p2) = (r, j)
  · rw [h2, Equiv.swap_apply_right]
    simp [pat, hj]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
  simp only [pat]
  by_cases hr : p1 = r
  · subst hr
    have h1' : p2 ≠ m p1 := fun h => h1 (by rw [h])
    have h2' : p2 ≠ j := fun h => h2 (by rw [h])
    simp [h1', h2']
  · simp [Function.update_of_ne hr]

theorem row_mem {e : Site L × Site L} :
    e ∈ rowEdges L ↔ e.1.1 = e.2.1 ∧ (e.1.2 : ℕ) + 1 = (e.2.2 : ℕ) := by
  simp [rowEdges]

/-- A swap along an admissible row edge maps patterns to patterns. -/
theorem pat_swap_edge (m : Fin L → Fin L) {e : Site L × Site L} (he : e ∈ rowEdges L)
    (hD : pat m e.1 ≠ pat m e.2) : ∃ m', pat m ∘ Equiv.swap e.1 e.2 = pat m' := by
  obtain ⟨⟨r, j⟩, ⟨r', j'⟩⟩ := e
  rw [row_mem] at he
  obtain ⟨hrr, hjj⟩ := he
  simp only at hrr hjj hD ⊢
  subst hrr
  by_cases h1 : j = m r
  · subst h1
    refine ⟨_, pat_swap m r j' ?_⟩
    intro h; rw [← h] at hjj; omega
  · by_cases h2 : j' = m r
    · subst h2
      refine ⟨Function.update m r j, ?_⟩
      rw [Equiv.swap_comm]
      exact pat_swap m r j h1
    · exfalso; apply hD; simp [pat, h1, h2]

theorem edge_sum (m : Fin L → Fin L) (G : Site L × Site L → ℂ) :
    ∑ e ∈ (rowEdges L).filter
        (fun e => pat m e.1 ≠ 0 ∧ pat m e.2 ≠ 0 ∧ pat m e.1 ≠ pat m e.2), G e =
      ∑ r : Fin L, ((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then G ((r, m r), (r, j')) else 0) +
        (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then G ((r, j), (r, m r)) else 0)) := by
  rw [Finset.sum_filter]
  unfold rowEdges
  rw [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Fintype.sum_prod_type]
  have hx1 : ∀ x : Fin L, (∑ x_1 : Fin L, ∑ x_2 : Fin L,
      if r = x_1 ∧ (x : ℕ) + 1 = (x_2 : ℕ) then
        (if pat m (r, x) ≠ 0 ∧ pat m (x_1, x_2) ≠ 0 ∧ pat m (r, x) ≠ pat m (x_1, x_2)
          then G ((r, x), x_1, x_2) else 0) else 0) =
      ∑ x_2 : Fin L, if (x : ℕ) + 1 = (x_2 : ℕ) then
        (if pat m (r, x) ≠ 0 ∧ pat m (r, x_2) ≠ 0 ∧ pat m (r, x) ≠ pat m (r, x_2)
          then G ((r, x), (r, x_2)) else 0) else 0 := by
    intro x
    rw [Finset.sum_eq_single r]
    · simp
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro x2 _
      rw [if_neg]
      rintro ⟨h, -⟩; exact hb h.symm
    · simp
  simp only [hx1]
  have key : ∀ j j' : Fin L,
      (if (j : ℕ) + 1 = (j' : ℕ) then
        (if pat m (r, j) ≠ 0 ∧ pat m (r, j') ≠ 0 ∧ pat m (r, j) ≠ pat m (r, j')
          then G ((r, j), (r, j')) else 0) else 0) =
      (if j = m r then (if (j' : ℕ) = (j : ℕ) + 1 then G ((r, j), (r, j')) else 0) else 0) +
      (if j' = m r then (if (j' : ℕ) = (j : ℕ) + 1 then G ((r, j), (r, j')) else 0) else 0) := by
    intro j j'
    by_cases hjj : (j : ℕ) + 1 = (j' : ℕ)
    · have hne : j ≠ j' := fun h => by rw [h] at hjj; omega
      by_cases h1 : j = m r
      · have h2 : j' ≠ m r := fun h => hne (h1.trans h.symm)
        subst h1; simp [pat, h2, hjj.symm, Ne.symm hne]
      · by_cases h2 : j' = m r
        · have h3 : (j : ℕ) + 1 = (m r : ℕ) := h2 ▸ hjj
          simp [pat, h1, h2, h3]
        · simp [pat, h1, h2, hjj]
    · have : ¬ (j' : ℕ) = (j : ℕ) + 1 := fun h => hjj h.symm
      simp [hjj, this]
  simp only [key, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single (m r)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_comm, Finset.sum_eq_single (m r)]
    · simp
    · intro b _ hb; simp [hb]
    · simp

theorem fin_sum_val {β : Type*} [AddCommMonoid β] (n : ℕ) (f : ℕ → β) :
    (∑ j : Fin L, if (j : ℕ) = n then f (j : ℕ) else 0) = if n < L then f n else 0 := by
  by_cases h : n < L
  · rw [if_pos h, Finset.sum_eq_single (⟨n, h⟩ : Fin L)]
    · simp
    · intro b _ hb
      rw [if_neg]; intro hh; exact hb (Fin.ext hh)
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]; intro hh; exact h (hh ▸ j.2)

theorem cos_pair (x t : ℝ) : Real.cos (x + t) + Real.cos (x - t) = 2 * Real.cos t * Real.cos x := by
  rw [Real.cos_add, Real.cos_sub]; ring

noncomputable def ph (L : ℕ) (k : ℕ) (j : ℕ) : ℝ :=
  Real.cos (Real.pi * (k : ℝ) * (2 * (j : ℝ) + 1) / (2 * (L : ℝ)))

theorem row_id (hL : 2 ≤ L) (k : ℕ) (j : Fin L) :
    (∑ j' : Fin L, if (j' : ℕ) = (j : ℕ) + 1 then (ph L k j - ph L k j') else 0) +
      (∑ j' : Fin L, if (j : ℕ) = (j' : ℕ) + 1 then (ph L k j - ph L k j') else 0) =
      2 * (1 - Real.cos (Real.pi * (k : ℝ) / (L : ℝ))) * ph L k j := by
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  set θ := Real.pi * (k : ℝ) / (L : ℝ) with hθ
  have harg : ∀ t : ℝ, Real.pi * (k : ℝ) * (2 * t + 1) / (2 * (L : ℝ)) =
      θ * (2 * t + 1) / 2 := by intro t; rw [hθ]; field_simp
  have hph : ∀ n : ℕ, ph L k n = Real.cos (θ * (2 * (n : ℝ) + 1) / 2) := by
    intro n; unfold ph; rw [harg]
  -- the recursion, with reflected ghost values at both ends
  have hstep : ∀ t : ℝ, Real.cos (θ * (2 * (t + 1) + 1) / 2) + Real.cos (θ * (2 * (t - 1) + 1) / 2)
      = 2 * Real.cos θ * Real.cos (θ * (2 * t + 1) / 2) := by
    intro t
    rw [← cos_pair]; congr 1 <;> congr 1 <;> ring
  have hright : Real.cos (θ * (2 * (L : ℝ) + 1) / 2) = Real.cos (θ * (2 * ((L : ℝ) - 1) + 1) / 2) := by
    have e1 : θ * (2 * (L : ℝ) + 1) / 2 = (k : ℝ) * Real.pi + θ / 2 := by rw [hθ]; field_simp; try ring
    have e2 : θ * (2 * ((L : ℝ) - 1) + 1) / 2 = (k : ℝ) * Real.pi - θ / 2 := by rw [hθ]; field_simp; try ring
    rw [e1, e2, Real.cos_add, Real.cos_sub, Real.sin_nat_mul_pi]; ring
  rw [fin_sum_val (L := L) ((j : ℕ) + 1) (fun n => ph L k j - ph L k n)]
  have hsecond : (∑ j' : Fin L, if (j : ℕ) = (j' : ℕ) + 1 then (ph L k j - ph L k j') else 0) =
      if 0 < (j : ℕ) then ph L k j - ph L k ((j : ℕ) - 1) else 0 := by
    by_cases h0 : 0 < (j : ℕ)
    · rw [if_pos h0]
      have : ∀ j' : Fin L, ((j : ℕ) = (j' : ℕ) + 1 ↔ (j' : ℕ) = (j : ℕ) - 1) := by
        intro j'; omega
      simp only [this]
      rw [fin_sum_val (L := L) ((j : ℕ) - 1) (fun n => ph L k j - ph L k n), if_pos (by omega)]
    · rw [if_neg h0]
      apply Finset.sum_eq_zero; intro j' _; rw [if_neg]; omega
  rw [hsecond]
  have hjL := j.2
  by_cases h1 : (j : ℕ) + 1 < L
  · by_cases h0 : 0 < (j : ℕ)
    · rw [if_pos h1, if_pos h0, hph, hph, hph]
      have := hstep (j : ℝ)
      push_cast [Nat.cast_sub (show 1 ≤ (j : ℕ) by omega)]
      push_cast at this
      linarith
    · rw [if_pos h1, if_neg h0]
      have hj0 : (j : ℕ) = 0 := by omega
      rw [hph, hph, hj0]
      have := hstep 0
      have hl : Real.cos (θ * (2 * ((0 : ℝ) - 1) + 1) / 2) = Real.cos (θ * (2 * (0 : ℝ) + 1) / 2) := by
        rw [show θ * (2 * ((0 : ℝ) - 1) + 1) / 2 = -(θ * (2 * (0 : ℝ) + 1) / 2) by ring, Real.cos_neg]
      push_cast at this ⊢
      linarith
  · have hjl : (j : ℕ) = L - 1 := by omega
    have h0 : 0 < (j : ℕ) := by omega
    rw [if_neg h1, if_pos h0, hph, hph]
    have := hstep (j : ℝ)
    have hjr : ((j : ℕ) : ℝ) = (L : ℝ) - 1 := by
      rw [hjl, Nat.cast_sub (by omega)]; simp
    have hr2 : Real.cos (θ * (2 * ((j : ℕ) + 1 : ℝ) + 1) / 2) = Real.cos (θ * (2 * ((j : ℕ) : ℝ) + 1) / 2) := by
      rw [show ((j : ℕ) + 1 : ℝ) = (L : ℝ) by rw [hjr]; ring, hjr]; exact hright
    push_cast [Nat.cast_sub (show 1 ≤ (j : ℕ) by omega)]
    push_cast at this hr2
    linarith

noncomputable def Wm (k : Fin L → Fin L) (m : Fin L → Fin L) : ℂ :=
  ∏ r : Fin L, ((ph L (k r) (m r) : ℝ) : ℂ)

noncomputable def vM (k : Fin L → Fin L) (c : Config L 3) : ℂ :=
  ∑ m : Fin L → Fin L, if c = pat m then Wm k m else 0

theorem vM_pat (k m : Fin L → Fin L) : vM k (pat m) = Wm k m := by
  unfold vM
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb; rw [if_neg]; intro h; exact hb (pat_inj h).symm
  · simp

theorem vM_nonpat (k : Fin L → Fin L) {c : Config L 3} (hc : ∀ m, c ≠ pat m) : vM k c = 0 := by
  unfold vM; apply Finset.sum_eq_zero; intro m _; rw [if_neg (hc m)]

theorem Wm_update (k m : Fin L → Fin L) (r j : Fin L) :
    Wm k (Function.update m r j) = ((ph L (k r) j : ℝ) : ℂ) *
      ∏ r' ∈ Finset.univ \ {r}, ((ph L (k r') (m r') : ℝ) : ℂ) := by
  unfold Wm
  have : (fun r' => ((ph L (k r') (Function.update m r j r') : ℝ) : ℂ)) =
      Function.update (fun r' => ((ph L (k r') (m r') : ℝ) : ℂ)) r ((ph L (k r) j : ℝ) : ℂ) := by
    funext r'
    by_cases h : r' = r
    · subst h; simp
    · simp [Function.update_of_ne h]
  rw [this, Finset.prod_update_of_mem (Finset.mem_univ r)]

theorem Wm_self (k m : Fin L → Fin L) (r : Fin L) :
    Wm k m = ((ph L (k r) (m r) : ℝ) : ℂ) *
      ∏ r' ∈ Finset.univ \ {r}, ((ph L (k r') (m r') : ℝ) : ℂ) := by
  rw [← Wm_update]; simp

theorem magnon_eig {a b : ℝ} (hL : 2 ≤ L) (k : Fin L → Fin L) :
    (switchHam L a b).mulVec (vM k) =
      ((a * (L : ℝ) ^ 2 + ∑ r : Fin L, 2 * b * (1 - Real.cos (Real.pi * ((k r : ℕ) : ℝ) / (L : ℝ))) : ℝ) : ℂ)
        • vM k := by
  funext c
  rw [Hv_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hc : ∃ m, c = pat m
  · obtain ⟨m, rfl⟩ := hc
    rw [vM_pat, pot_pat]
    unfold S
    rw [rate_sum, edge_sum]
    have hcard : (((rowEdges L).filter (fun e => pat m e.1 ≠ 0 ∧ pat m e.2 ≠ 0 ∧
        pat m e.1 ≠ pat m e.2)).card : ℂ) = ∑ e ∈ (rowEdges L).filter (fun e => pat m e.1 ≠ 0 ∧
        pat m e.2 ≠ 0 ∧ pat m e.1 ≠ pat m e.2), (1 : ℂ) := by simp
    push_cast
    rw [hcard, edge_sum]
    -- rewrite the swapped configurations as patterns
    have hR : ∀ r : Fin L, (∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then
        vM k (pat m ∘ Equiv.swap (r, m r) (r, j')) else 0) =
        ∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then Wm k (Function.update m r j') else 0 := by
      intro r; apply Finset.sum_congr rfl; intro j' _
      split_ifs with h
      · rw [pat_swap m r j' (fun h' => by rw [h'] at h; omega), vM_pat]
      · rfl
    have hLf : ∀ r : Fin L, (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then
        vM k (pat m ∘ Equiv.swap (r, j) (r, m r)) else 0) =
        ∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then Wm k (Function.update m r j) else 0 := by
      intro r; apply Finset.sum_congr rfl; intro j _
      split_ifs with h
      · rw [Equiv.swap_comm, pat_swap m r j (fun h' => by rw [h'] at h; omega), vM_pat]
      · rfl
    simp only [Function.comp_def] at hR hLf ⊢
    simp only [hR, hLf]
    have hrow : ∀ r : Fin L, (b : ℂ) * (((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then (1 : ℂ) else 0) +
        (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0)) * Wm k m -
        ((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then Wm k (Function.update m r j') else 0) +
         (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then Wm k (Function.update m r j) else 0))) =
        2 * (b : ℂ) * (1 - Complex.cos (↑Real.pi * ((k r : ℕ) : ℂ) / (L : ℂ))) * Wm k m := by
      intro r
      have hr := congrArg Complex.ofReal (row_id hL (k r) (m r))
      push_cast at hr
      simp only [apply_ite Complex.ofReal, Complex.ofReal_sub, Complex.ofReal_zero] at hr
      rw [Wm_self k m r]
      simp only [Wm_update]
      set Q := ∏ r' ∈ Finset.univ \ {r}, ((ph L (k r') (m r') : ℝ) : ℂ)
      have e1 : ((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then (1 : ℂ) else 0) +
          (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0)) *
            (((ph L (k r) (m r) : ℝ) : ℂ) * Q) -
          ((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then ((ph L (k r) j' : ℝ) : ℂ) * Q else 0) +
           (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then ((ph L (k r) j : ℝ) : ℂ) * Q else 0)) =
          Q * ((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then
              (((ph L (k r) (m r) : ℝ) : ℂ) - ((ph L (k r) j' : ℝ) : ℂ)) else 0) +
            (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then
              (((ph L (k r) (m r) : ℝ) : ℂ) - ((ph L (k r) j : ℝ) : ℂ)) else 0)) := by
        simp only [add_mul, Finset.sum_mul, Finset.mul_sum, mul_add]
        rw [add_sub_add_comm, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> split_ifs <;> ring
      rw [e1, hr]
      ring
    have hR2 : ((a : ℂ) * (L : ℂ) ^ 2 + ∑ x : Fin L, 2 * (b : ℂ) *
        (1 - Complex.cos (↑Real.pi * ((k x : ℕ) : ℂ) / (L : ℂ)))) * Wm k m =
        (a : ℂ) * (L : ℂ) ^ 2 * Wm k m + ∑ r : Fin L, (b : ℂ) *
          (((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then (1 : ℂ) else 0) +
          (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then (1 : ℂ) else 0)) * Wm k m -
          ((∑ j' : Fin L, if (j' : ℕ) = (m r : ℕ) + 1 then Wm k (Function.update m r j') else 0) +
           (∑ j : Fin L, if (m r : ℕ) = (j : ℕ) + 1 then Wm k (Function.update m r j) else 0))) := by
      rw [add_mul, Finset.sum_mul]
      simp only [hrow]
    rw [hR2]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  · push_neg at hc
    rw [vM_nonpat k hc]
    have hz : ∀ e ∈ (rowEdges L).filter (fun e => c e.1 ≠ 0 ∧ c e.2 ≠ 0 ∧ c e.1 ≠ c e.2),
        vM k (c ∘ Equiv.swap e.1 e.2) = 0 := by
      intro e he
      rw [Finset.mem_filter] at he
      apply vM_nonpat
      intro m' hm'
      have hc' : c = pat m' ∘ Equiv.swap e.1 e.2 := by
        rw [← hm']; funext x; simp
      have hD : pat m' e.1 ≠ pat m' e.2 := by
        rw [← hm']; simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
        exact fun h => he.2.2.2 h.symm
      obtain ⟨m'', h''⟩ := pat_swap_edge m' he.1 hD
      exact hc m'' (hc'.trans h'')
    rw [Finset.sum_eq_zero hz]
    simp

theorem vM_ne_zero (hL : 2 ≤ L) (k : Fin L → Fin L) : vM k ≠ 0 := by
  intro h
  have h0 := congrFun h (pat (fun _ => ⟨0, by omega⟩))
  rw [vM_pat] at h0
  unfold Wm at h0
  rw [Pi.zero_apply, Finset.prod_eq_zero_iff] at h0
  obtain ⟨r, -, hr⟩ := h0
  rw [Complex.ofReal_eq_zero] at hr
  revert hr
  apply ne_of_gt
  unfold ph
  apply Real.cos_pos_of_mem_Ioo
  have hk := (k r).2
  have hL0 : (0 : ℝ) < L := by positivity
  have hkL : ((k r : ℕ) : ℝ) < L := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ ((k r : ℕ) : ℝ) := by positivity
  constructor
  · have : 0 ≤ Real.pi * ((k r : ℕ) : ℝ) * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (L : ℝ)) := by
      apply div_nonneg _ (by positivity); simp; positivity
    linarith [Real.pi_pos]
  · rw [div_lt_iff₀ (by positivity)]
    simp
    nlinarith [Real.pi_pos]

end AgentBUSG

open AgentBUSG in
theorem _root_.solution
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    ∀ L : ℕ, 2 ≤ L →
      ∀ s ∈ switchMagnonSpectrum L b,
        a * (L : ℝ) ^ 2 + s ∈ specReal (switchHam L a b) := by
  intro L hL s hs
  obtain ⟨k, rfl⟩ := hs
  exact mem_of_eig (vM k) (vM_ne_zero hL k) (magnon_eig hL k)

#print axioms solution
