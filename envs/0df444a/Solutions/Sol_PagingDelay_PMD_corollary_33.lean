-- Prove2me | solution 1 for PagingDelay.PMD.corollary_33
-- status  : ACCEPTED   (prove)
-- author  : @licsth
-- created : 2026-11-14T11:05:15.033198+00:00
-- url     : https://prove2.me/submissions/6c6bc0e0-a6b1-42b3-b348-e7a3e8832a65

import Mathlib
import Definitions.Def_PagingDelay_PMD_Rounding

/-! ## Inlined from `BBNProof.Defs` -/
section

/-!
# Online rounding for weighted paging (Bansal–Buchbinder–Naor): shared definitions

This library proves, from scratch, a version of the online rounding theorem of Bansal, Buchbinder
and Naor (*A primal-dual randomized algorithm for weighted paging*, Theorem 4.1) that suffices for
`PagingDelay.PMD.corollary_33`, and realizes the rounding with per-seed online maps.

## The class `𝒟(y)` (BBN, proof of Theorem 4.1)

Pages are grouped into *weight classes* `v` (the distinct values of `w`). For a fractional cache `y`
let `S_≤(v) = ∑_{w q ≤ v} y q` and `S_<(v) = ∑_{w q < v} y q`. For `α ∈ [0,1)` the cache `C(α)` of
BBN holds `n_v(α) = ⌈S_≤(v) - α⌉ - ⌈S_<(v) - α⌉` pages of class `v` (the number of points of
`α + ℤ` in the class interval `[S_<(v), S_≤(v))`). We only remember the *law* of this profile:
`D ∈ 𝒟(y)` iff the class profile of a cache drawn from `D` has the law of `n(α)` for uniform `α`,
and the marginals of `D` are `y`.

## Per-seed realization

Seeds are sequences `ω : ℕ → ℝ` of independent uniform `[0,1)` variables; step `ν` draws the next
cache from a finite distribution by inverse-CDF sampling with `ω ν`.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped BigOperators

namespace BBNProof

section Pages

variable {Page : Type} [Fintype Page] [DecidableEq Page]

/-- `𝒫`: fractional caches `y ∈ [0,1]ⁿ` with total mass `k`. -/
def fracCaches (k : ℕ) : Set (Page → ℝ) :=
  {y | (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ ∑ i, y i = k}

/-- The indicator vector of a set of pages. -/
def indicator (C : Finset Page) (i : Page) : ℝ := if i ∈ C then 1 else 0

/-- `Π(Q)`: the marginals `Pr_{C ∼ Q}[i ∈ C]`. -/
def marginal (Q : PMF (Finset Page)) (i : Page) : ℝ :=
  ∑ C : Finset Page, if i ∈ C then (Q C).toReal else 0

/-- The weight classes: the distinct values of `w`. -/
abbrev WClass (w : Page → ℝ) := {v : ℝ // v ∈ Finset.univ.image w}

/-- A class profile: a number of pages for each weight class (at most the number of pages). -/
abbrev Prof (w : Page → ℝ) := WClass w → Fin (Fintype.card Page + 1)

/-- The pages of weight `v`. -/
def cls (w : Page → ℝ) (v : ℝ) : Finset Page := Finset.univ.filter (fun q => w q = v)

/-- The mass of `y` on the class of weight `v`. -/
def classMass (w y : Page → ℝ) (v : ℝ) : ℝ := ∑ q ∈ cls w v, y q

/-- The class profile of a cache: the number of its pages in each weight class. -/
def profile (w : Page → ℝ) (C : Finset Page) : Prof w := fun v =>
  ⟨(C ∩ cls w v).card, Nat.lt_succ_of_le (Finset.card_le_univ _)⟩

/-- `S_≤(v)`: the mass of `y` on pages of weight at most `v`. -/
def massLE (w y : Page → ℝ) (v : ℝ) : ℝ := ∑ q ∈ Finset.univ.filter (fun q => w q ≤ v), y q

/-- `S_<(v)`: the mass of `y` on pages of weight less than `v`. -/
def massLT (w y : Page → ℝ) (v : ℝ) : ℝ := ∑ q ∈ Finset.univ.filter (fun q => w q < v), y q

/-- BBN's profile at `α`: `n_v(α) = ⌈S_≤(v) - α⌉ - ⌈S_<(v) - α⌉` (truncated to `[0, #pages]`,
which never bites for fractional caches and `α ∈ [0,1)`). -/
def slots (w y : Page → ℝ) (α : ℝ) : Prof w := fun v =>
  ⟨min (⌈massLE w y v - α⌉ - ⌈massLT w y v - α⌉).toNat (Fintype.card Page), by omega⟩

end Pages

/-- The uniform distribution on `[0,1)`. -/
def unif : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance : IsProbabilityMeasure unif := ⟨by simp [unif]⟩

section Laws

variable {Page : Type} [Fintype Page] [DecidableEq Page]

theorem measurable_slots (w y : Page → ℝ) : Measurable (slots w y) := by
  refine measurable_pi_lambda _ fun v => ?_
  have h1 : Measurable fun α : ℝ => ⌈massLE w y v - α⌉ :=
    Int.measurable_ceil.comp (measurable_const.sub measurable_id)
  have h2 : Measurable fun α : ℝ => ⌈massLT w y v - α⌉ :=
    Int.measurable_ceil.comp (measurable_const.sub measurable_id)
  exact (Measurable.of_discrete (f := fun z : ℤ × ℤ =>
    (⟨min (z.1 - z.2).toNat (Fintype.card Page), by omega⟩ : Fin (Fintype.card Page + 1)))).comp
    (h1.prodMk h2)

instance (w y : Page → ℝ) : IsProbabilityMeasure (unif.map (slots w y)) :=
  Measure.isProbabilityMeasure_map (measurable_slots w y).aemeasurable

instance (w y y' : Page → ℝ) :
    IsProbabilityMeasure (unif.map (fun α => (slots w y α, slots w y' α))) :=
  Measure.isProbabilityMeasure_map ((measurable_slots w y).prodMk (measurable_slots w y')).aemeasurable

/-- The law of BBN's profile `n(α)` for uniform `α ∈ [0,1)`. -/
def profLaw (w y : Page → ℝ) : PMF (Prof w) := (unif.map (slots w y)).toPMF

/-- The coupling of the profiles for `y` and `y'` through the same `α`. -/
def rhoLaw (w y y' : Page → ℝ) : PMF (Prof w × Prof w) :=
  (unif.map (fun α => (slots w y α, slots w y' α))).toPMF

/-- `𝒟(y)`: the profile of the cache has the law of BBN's `n(α)`, and the marginals are `y`. -/
def InClass (w y : Page → ℝ) (D : PMF (Finset Page)) : Prop :=
  D.map (profile w) = profLaw w y ∧ marginal D = y

/-- The marginals of the cache coordinate of a distribution on (cache, target profile) pairs. -/
def margX {w : Page → ℝ} (μ : PMF (Finset Page × Prof w)) (i : Page) : ℝ :=
  ∑ x, (μ x).toReal * (if i ∈ x.1 then 1 else 0)

end Laws

section Sampling

variable {S : Type} [Fintype S]

/-- The mass of the outcomes before `s` in the enumeration `Fintype.equivFin S`. -/
def cumBefore (p : PMF S) (s : S) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => Fintype.equivFin S t < Fintype.equivFin S s), (p t).toReal

open Classical in
/-- Inverse-CDF sampling: the outcome `s` with `u ∈ [cumBefore p s, cumBefore p s + p s)`
(an element of the support if there is none, i.e. for `u ∉ [0,1)`). -/
def sample (p : PMF S) (u : ℝ) : S :=
  if h : ∃ s, p s ≠ 0 ∧ cumBefore p s ≤ u ∧ u < cumBefore p s + (p s).toReal then h.choose
  else p.support_nonempty.some

variable {Y : Type}

/-- The law of the current state after the history `ys` (given in reverse order): start in `s₀`
(after the first entry), then draw the state after `y` from `step D ys y s`, where `D` is the
law of the current state `s` and `ys` the history so far (in order). -/
def lawRev (s₀ : S) (step : PMF S → List Y → Y → S → PMF S) : List Y → PMF S
  | [] => PMF.pure s₀
  | [_] => PMF.pure s₀
  | y :: y' :: rest =>
    (lawRev s₀ step (y' :: rest)).bind (step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y)

/-- The state of seed `ω` after the history (given in reverse order); step `ν` uses `ω ν`. -/
def runRev (s₀ : S) (step : PMF S → List Y → Y → S → PMF S) (ω : ℕ → ℝ) : List Y → S
  | [] => s₀
  | [_] => s₀
  | y :: y' :: rest =>
    sample (step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y
      (runRev s₀ step ω (y' :: rest))) (ω rest.length)

/-- The law of the state after the history `ys`. -/
def lawOf (s₀ : S) (step : PMF S → List Y → Y → S → PMF S) (ys : List Y) : PMF S :=
  lawRev s₀ step ys.reverse

/-- The state of seed `ω` after the history `ys`. It depends only on `ys` (online). -/
def run (s₀ : S) (step : PMF S → List Y → Y → S → PMF S) (ω : ℕ → ℝ) (ys : List Y) : S :=
  runRev s₀ step ω ys.reverse

end Sampling

/-- The law of the seeds: independent uniform `[0,1)` variables. -/
def seedLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => unif)

instance : IsProbabilityMeasure seedLaw := by
  unfold seedLaw; infer_instance

end BBNProof
end

/-! ## Inlined from `BBNProof.Realize` -/
section

/-!
# Per-seed realization of a chain of kernels

Inverse-CDF sampling with a uniform seed coordinate has the right law, and the seed coordinates
are independent under `seedLaw`; hence `run` realizes `lawOf` and couples consecutive states by
the step kernel.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BBNProof.Realize

section Sampling

variable {S : Type} [Fintype S]

lemma cumBefore_nonneg (p : PMF S) (s : S) : 0 ≤ cumBefore p s :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

lemma sum_toReal (p : PMF S) : ∑ t, (p t).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun t _ => PMF.apply_ne_top p t), h]
  simp

lemma cumBefore_add_le (p : PMF S) (s : S) : cumBefore p s + (p s).toReal ≤ 1 := by
  classical
  rw [← sum_toReal p, cumBefore, add_comm,
    ← Finset.sum_insert (f := fun t => (p t).toReal) (a := s)
      (s := Finset.univ.filter fun t => Fintype.equivFin S t < Fintype.equivFin S s) (by simp)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ => ENNReal.toReal_nonneg)

lemma cumBefore_lt (p : PMF S) {t s : S} (h : Fintype.equivFin S t < Fintype.equivFin S s) :
    cumBefore p t + (p t).toReal ≤ cumBefore p s := by
  classical
  unfold cumBefore
  rw [add_comm, ← Finset.sum_insert (f := fun t => (p t).toReal) (a := t)
      (s := Finset.univ.filter fun x => Fintype.equivFin S x < Fintype.equivFin S t) (by simp)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | hx
    · exact h
    · exact hx.trans h
  · intros; exact ENNReal.toReal_nonneg

/-- `u` lies in the (nonempty) sampling interval of `s`. -/
def Mem (p : PMF S) (s : S) (u : ℝ) : Prop :=
  p s ≠ 0 ∧ cumBefore p s ≤ u ∧ u < cumBefore p s + (p s).toReal

lemma mem_unique (p : PMF S) {t s : S} {u : ℝ} (ht : Mem p t u) (hs : Mem p s u) : t = s := by
  by_contra hne
  have : Fintype.equivFin S t ≠ Fintype.equivFin S s :=
    fun h => hne ((Fintype.equivFin S).injective h)
  rcases lt_or_gt_of_ne this with h | h
  · linarith [cumBefore_lt p h, ht.2.2, hs.2.1]
  · linarith [cumBefore_lt p h, hs.2.2, ht.2.1]

lemma sample_eq_iff (p : PMF S) (u : ℝ) (s : S) :
    sample p u = s ↔ Mem p s u ∨ ((¬ ∃ t, Mem p t u) ∧ p.support_nonempty.some = s) := by
  unfold sample
  by_cases h : ∃ t, Mem p t u
  · have h' : ∃ s, p s ≠ 0 ∧ cumBefore p s ≤ u ∧ u < cumBefore p s + (p s).toReal := h
    rw [dif_pos h']
    constructor
    · rintro rfl; exact Or.inl h'.choose_spec
    · rintro (hs | ⟨hn, _⟩)
      · exact mem_unique p h'.choose_spec hs
      · exact absurd h hn
  · have h' : ¬ ∃ s, p s ≠ 0 ∧ cumBefore p s ≤ u ∧ u < cumBefore p s + (p s).toReal := h
    rw [dif_neg h']
    constructor
    · intro e; exact Or.inr ⟨h, e⟩
    · rintro (hs | ⟨_, e⟩)
      · exact absurd ⟨s, hs⟩ h
      · exact e

lemma sample_mem_support (p : PMF S) (u : ℝ) : sample p u ∈ p.support := by
  rcases (sample_eq_iff p u (sample p u)).1 rfl with h | ⟨_, h⟩
  · exact (PMF.mem_support_iff _ _).2 h.1
  · rw [← h]; exact p.support_nonempty.some_mem

lemma measurableSet_mem (p : PMF S) (s : S) : MeasurableSet {u | Mem p s u} := by
  by_cases h : p s = 0
  · have : {u | Mem p s u} = ∅ := by ext u; simp [Mem, h]
    rw [this]; exact MeasurableSet.empty
  · have : {u | Mem p s u} = Set.Ico (cumBefore p s) (cumBefore p s + (p s).toReal) := by
      ext u; simp [Mem, h]
    rw [this]; exact measurableSet_Ico

lemma measurableSet_sample (p : PMF S) (s : S) : MeasurableSet {u | sample p u = s} := by
  have : {u | sample p u = s} = {u | Mem p s u} ∪
      ((⋃ t, {u | Mem p t u})ᶜ ∩ {_u | p.support_nonempty.some = s}) := by
    ext u; simp [sample_eq_iff]
  rw [this]
  exact (measurableSet_mem p s).union
    ((MeasurableSet.iUnion fun t => measurableSet_mem p t).compl.inter (MeasurableSet.const _))

lemma le_unif_sample (p : PMF S) (s : S) : p s ≤ unif {u | sample p u = s} := by
  by_cases h : p s = 0
  · rw [h]; simp
  have hsub : Set.Ico (cumBefore p s) (cumBefore p s + (p s).toReal) ⊆
      {u | sample p u = s} ∩ Set.Ico 0 1 := by
    intro u hu
    refine ⟨(sample_eq_iff p u s).2 (Or.inl ⟨h, hu.1, hu.2⟩), ?_, ?_⟩
    · linarith [cumBefore_nonneg p s, hu.1]
    · linarith [cumBefore_add_le p s, hu.2]
  calc p s = volume (Set.Ico (cumBefore p s) (cumBefore p s + (p s).toReal)) := by
          rw [Real.volume_Ico, add_sub_cancel_left, ENNReal.ofReal_toReal (PMF.apply_ne_top p s)]
    _ ≤ volume ({u | sample p u = s} ∩ Set.Ico 0 1) := measure_mono hsub
    _ = unif {u | sample p u = s} := by
          rw [unif, Measure.restrict_apply (measurableSet_sample p s)]

/-- Inverse-CDF sampling with a uniform `[0,1)` variable has law `p`. -/
lemma unif_sample (p : PMF S) (s : S) : unif {u | sample p u = s} = p s := by
  classical
  have hsum : ∑ t, unif {u | sample p u = t} = 1 := by
    have := sum_measure_preimage_singleton (μ := unif) (Finset.univ : Finset S) (f := sample p)
      (fun t _ => measurableSet_sample p t)
    simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at this
    exact this
  have hp : ∑ t, p t = 1 := by
    have h := p.tsum_coe
    rwa [tsum_fintype] at h
  refine le_antisymm ?_ (le_unif_sample p s)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at hsum hp
  have hle : ∑ t ∈ Finset.univ.erase s, p t ≤
      ∑ t ∈ Finset.univ.erase s, unif {u | sample p u = t} :=
    Finset.sum_le_sum fun t _ => le_unif_sample p t
  have hne : ∑ t ∈ Finset.univ.erase s, p t ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun t _ => PMF.apply_ne_top p t
  refine ENNReal.le_of_add_le_add_right hne ?_
  calc _ ≤ unif {u | sample p u = s} + ∑ t ∈ Finset.univ.erase s, unif {u | sample p u = t} := by
        gcongr
    _ = _ := by rw [hsum, hp]

end Sampling

section Seeds

/-- The σ-algebra of the seed coordinate `i`. -/
def coordSigma (i : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun ω : ℕ → ℝ => ω i) inferInstance

/-- The σ-algebra of the seed coordinates `< n`. -/
def past (n : ℕ) : MeasurableSpace (ℕ → ℝ) := ⨆ i ∈ Set.Iio n, coordSigma i

lemma coordSigma_le (i : ℕ) : coordSigma i ≤ MeasurableSpace.pi :=
  (measurable_pi_apply i).comap_le

lemma past_le (n : ℕ) : past n ≤ MeasurableSpace.pi := iSup₂_le fun i _ => coordSigma_le i

lemma coordSigma_le_past {i n : ℕ} (h : i < n) : coordSigma i ≤ past n :=
  le_iSup₂ (f := fun i (_ : i ∈ Set.Iio n) => coordSigma i) i h

lemma past_mono {m n : ℕ} (h : m ≤ n) : past m ≤ past n :=
  iSup₂_le fun _ hi => coordSigma_le_past (lt_of_lt_of_le hi h)

lemma measurableSet_coord {i : ℕ} {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet[coordSigma i] {ω : ℕ → ℝ | ω i ∈ B} := ⟨B, hB, rfl⟩

lemma indep_past (n : ℕ) : Indep (past n) (coordSigma n) seedLaw := by
  have hi : iIndep coordSigma seedLaw := by
    have := iIndepFun_infinitePi (P := fun _ : ℕ => unif) (X := fun _ => id)
      (fun _ => measurable_id)
    exact (iIndepFun_iff_iIndep _ _ _).1 this
  have := indep_iSup_of_disjoint coordSigma_le hi (S := Set.Iio n) (T := {n})
    (Set.disjoint_singleton_right.2 (lt_irrefl n))
  simpa [past] using this

lemma seedLaw_inter {n : ℕ} {A : Set (ℕ → ℝ)} (hA : MeasurableSet[past n] A) {B : Set ℝ}
    (hB : MeasurableSet B) : seedLaw (A ∩ {ω | ω n ∈ B}) = seedLaw A * unif B := by
  rw [(Indep_iff _ _ _).1 (indep_past n) A _ hA (measurableSet_coord hB)]
  congr 1
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => unif) n).measure_preimage
    hB.nullMeasurableSet

end Seeds

section Chain

variable {S : Type} [Fintype S] [DecidableEq S] {Y : Type}
  (s₀ : S) (step : PMF S → List Y → Y → S → PMF S)

lemma runRev_cons_cons (ω : ℕ → ℝ) (y y' : Y) (rest : List Y) :
    runRev s₀ step ω (y :: y' :: rest) =
      sample (step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y
        (runRev s₀ step ω (y' :: rest))) (ω rest.length) := rfl

lemma lawRev_cons_cons (y y' : Y) (rest : List Y) :
    lawRev s₀ step (y :: y' :: rest) =
      (lawRev s₀ step (y' :: rest)).bind
        (step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y) := rfl

lemma set_runRev_cons_cons (y y' : Y) (rest : List Y) (s : S) :
    {ω | runRev s₀ step ω (y :: y' :: rest) = s} = ⋃ r, ({ω | runRev s₀ step ω (y' :: rest) = r} ∩
      {ω | ω rest.length ∈
        {u | sample (step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y r) u = s}}) := by
  ext ω; simp [runRev_cons_cons]

lemma runRev_mem_support (ω : ℕ → ℝ) :
    ∀ l : List Y, runRev s₀ step ω l ∈ (lawRev s₀ step l).support
  | [] => by simp [runRev, lawRev]
  | [_] => by simp [runRev, lawRev]
  | y :: y' :: rest => by
    rw [runRev_cons_cons, lawRev_cons_cons, PMF.mem_support_bind_iff]
    exact ⟨_, runRev_mem_support ω (y' :: rest), sample_mem_support _ _⟩

lemma measurableSet_runRev_past :
    ∀ (l : List Y) (s : S), MeasurableSet[past (l.length - 1)] {ω | runRev s₀ step ω l = s}
  | [], s => MeasurableSet.const (s₀ = s)
  | [_], s => MeasurableSet.const (s₀ = s)
  | y :: y' :: rest, s => by
    rw [set_runRev_cons_cons]
    refine MeasurableSet.iUnion fun r => MeasurableSet.inter ?_ ?_
    · exact past_mono (by simp) _ (measurableSet_runRev_past (y' :: rest) r)
    · exact coordSigma_le_past (by simp) _ (measurableSet_coord (measurableSet_sample _ _))

lemma measurableSet_runRev (l : List Y) (s : S) :
    MeasurableSet {ω | runRev s₀ step ω l = s} :=
  past_le _ _ (measurableSet_runRev_past s₀ step l s)

lemma seedLaw_runRev_cons_cons (y y' : Y) (rest : List Y) (r s : S) :
    seedLaw ({ω | runRev s₀ step ω (y' :: rest) = r} ∩
      {ω | ω rest.length ∈
        {u | sample (step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y r) u = s}}) =
      seedLaw {ω | runRev s₀ step ω (y' :: rest) = r} *
        step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y r s := by
  rw [seedLaw_inter (n := rest.length) (measurableSet_runRev_past s₀ step (y' :: rest) r) (measurableSet_sample _ _),
    unif_sample]

lemma seedLaw_runRev : ∀ (l : List Y) (s : S),
    seedLaw {ω | runRev s₀ step ω l = s} = lawRev s₀ step l s
  | [], s => by
    by_cases h : s = s₀
    · subst h; simp [runRev, lawRev]
    · simp [runRev, lawRev, h, Ne.symm h]
  | [_], s => by
    by_cases h : s = s₀
    · subst h; simp [runRev, lawRev]
    · simp [runRev, lawRev, h, Ne.symm h]
  | y :: y' :: rest, s => by
    rw [set_runRev_cons_cons, measure_iUnion, tsum_fintype, lawRev_cons_cons, PMF.bind_apply,
      tsum_fintype]
    · refine Finset.sum_congr rfl fun r _ => ?_
      rw [seedLaw_runRev_cons_cons, seedLaw_runRev (y' :: rest) r]
    · exact fun r r' hrr' => Set.disjoint_left.2 fun ω h1 h2 => hrr' (h1.1.symm.trans h2.1)
    · exact fun r => (measurableSet_runRev s₀ step _ r).inter
        (measurable_pi_apply _ (measurableSet_sample _ _))

lemma lintegral_runRev_pair (y y' : Y) (rest : List Y) (f : S → S → ENNReal) :
    ∫⁻ ω, f (runRev s₀ step ω (y' :: rest)) (runRev s₀ step ω (y :: y' :: rest)) ∂seedLaw =
      ∑ s, ∑ s', lawRev s₀ step (y' :: rest) s *
        step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y s s' * f s s' := by
  set X := fun ω => runRev s₀ step ω (y' :: rest) with hX
  set X' := fun ω => runRev s₀ step ω (y :: y' :: rest) with hX'
  have hset : ∀ s s', {ω | X ω = s ∧ X' ω = s'} = {ω | runRev s₀ step ω (y' :: rest) = s} ∩
      {ω | ω rest.length ∈
        {u | sample (step (lawRev s₀ step (y' :: rest)) (y' :: rest).reverse y s) u = s'}} := by
    intro s s'
    ext ω
    simp only [hX, hX', Set.mem_ofPred_eq, Set.mem_inter_iff, runRev_cons_cons]
    constructor
    · rintro ⟨h1, h2⟩; subst h1; exact ⟨rfl, h2⟩
    · rintro ⟨h1, h2⟩; subst h1; exact ⟨rfl, h2⟩
  have hmeas : ∀ s s', MeasurableSet {ω | X ω = s ∧ X' ω = s'} := fun s s' => by
    rw [hset]
    exact (measurableSet_runRev s₀ step _ s).inter
      (measurable_pi_apply _ (measurableSet_sample _ _))
  have hpt : ∀ ω, f (X ω) (X' ω) =
      ∑ s, ∑ s', Set.indicator {ω | X ω = s ∧ X' ω = s'} (fun _ => f s s') ω := by
    intro ω
    rw [Finset.sum_eq_single (X ω), Finset.sum_eq_single (X' ω)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro b _ hb
      exact Finset.sum_eq_zero fun s' _ => by simp [Ne.symm hb]
    · simp
  calc ∫⁻ ω, f (X ω) (X' ω) ∂seedLaw
      = ∫⁻ ω, ∑ s, ∑ s', Set.indicator {ω | X ω = s ∧ X' ω = s'} (fun _ => f s s') ω ∂seedLaw :=
        lintegral_congr fun ω => hpt ω
    _ = ∑ s, ∑ s', f s s' * seedLaw {ω | X ω = s ∧ X' ω = s'} := by
        rw [lintegral_finsetSum _ fun s _ =>
          Finset.measurable_sum _ fun s' _ => measurable_const.indicator (hmeas s s')]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [lintegral_finsetSum _ fun s' _ => measurable_const.indicator (hmeas s s')]
        exact Finset.sum_congr rfl fun s' _ => lintegral_indicator_const (hmeas s s') _
    _ = _ := by
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
        rw [hset, seedLaw_runRev_cons_cons, seedLaw_runRev]
        ring

end Chain

end BBNProof.Realize

namespace BBNProof

open Realize

variable {S : Type} [Fintype S] [DecidableEq S] {Y : Type}
  (s₀ : S) (step : PMF S → List Y → Y → S → PMF S)

theorem lawOf_singleton (y : Y) : lawOf s₀ step [y] = PMF.pure s₀ := rfl

theorem lawOf_snoc (ys : List Y) (hys : ys ≠ []) (y : Y) :
    lawOf s₀ step (ys ++ [y]) = (lawOf s₀ step ys).bind (step (lawOf s₀ step ys) ys y) := by
  obtain ⟨l, rfl⟩ : ∃ l, ys = l.reverse := ⟨ys.reverse, by simp⟩
  cases l with
  | nil => exact absurd rfl hys
  | cons y' rest =>
    simp only [lawOf, List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.singleton_append]
    exact lawRev_cons_cons s₀ step y y' rest

theorem run_singleton (ω : ℕ → ℝ) (y : Y) : run s₀ step ω [y] = s₀ := rfl

/-- Every seed follows the support of the chain. -/
theorem run_mem_support (ω : ℕ → ℝ) (ys : List Y) :
    run s₀ step ω ys ∈ (lawOf s₀ step ys).support :=
  runRev_mem_support s₀ step ω ys.reverse

theorem measurableSet_run (ys : List Y) (s : S) :
    MeasurableSet {ω : ℕ → ℝ | run s₀ step ω ys = s} :=
  measurableSet_runRev s₀ step ys.reverse s

/-- The state after `ys` has law `lawOf ys`. -/
theorem seedLaw_run (ys : List Y) (s : S) :
    seedLaw {ω | run s₀ step ω ys = s} = lawOf s₀ step ys s :=
  seedLaw_runRev s₀ step ys.reverse s

/-- Consecutive states are coupled by the step kernel. -/
theorem lintegral_run_pair (ys : List Y) (hys : ys ≠ []) (y : Y) (f : S → S → ENNReal) :
    ∫⁻ ω, f (run s₀ step ω ys) (run s₀ step ω (ys ++ [y])) ∂seedLaw =
      ∑ s, ∑ s', lawOf s₀ step ys s * step (lawOf s₀ step ys) ys y s s' * f s s' := by
  obtain ⟨l, rfl⟩ : ∃ l, ys = l.reverse := ⟨ys.reverse, by simp⟩
  cases l with
  | nil => exact absurd rfl hys
  | cons y' rest =>
    simp only [run, lawOf, List.reverse_append, List.reverse_reverse, List.reverse_singleton,
      List.singleton_append]
    exact lintegral_runRev_pair s₀ step y y' rest f

end BBNProof
end

/-! ## Inlined from `BBNProof.Profile` -/
section

/-! BBN's class profiles `n(α)` and their coupling: proofs of the interface
`BBNProof/Spec/Profile.lean`. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
set_option linter.unusedSectionVars false

namespace BBNProof.Profile
open BBNProof

variable {Page : Type} [Fintype Page] [DecidableEq Page]

/-! ### Generic measure glue -/

theorem sum_toPMF {β : Type} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (g : ℝ → β) (hg : Measurable g) [IsProbabilityMeasure (unif.map g)] (f : β → ℝ) :
    ∑ b, ((unif.map g).toPMF b).toReal * f b = ∫ α, f (g α) ∂unif := by
  rw [← integral_map hg.aemeasurable (measurable_of_finite f).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Measure.toPMF_apply, smul_eq_mul, measureReal_def]

theorem exists_of_mem_support {β : Type} [Fintype β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (g : ℝ → β) (hg : Measurable g)
    [IsProbabilityMeasure (unif.map g)] {b : β} (hb : b ∈ ((unif.map g).toPMF).support) :
    ∃ α ∈ Set.Ico (0 : ℝ) 1, g α = b := by
  rw [PMF.mem_support_iff, Measure.toPMF_apply, Measure.map_apply hg (measurableSet_singleton b),
    unif, Measure.restrict_apply (hg (measurableSet_singleton b))] at hb
  by_contra h
  apply hb
  have : g ⁻¹' {b} ∩ Set.Ico 0 1 = ∅ := by
    ext α
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    intro h1 h2
    exact h ⟨α, h2, h1⟩
  rw [this, measure_empty]

theorem map_toPMF {β γ : Type} [Fintype β] [Fintype γ] [MeasurableSpace β]
    [MeasurableSingletonClass β] [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (g : ℝ → β) (hg : Measurable g) [IsProbabilityMeasure (unif.map g)] (f : β → γ)
    (h : ℝ → γ) [IsProbabilityMeasure (unif.map h)] (hfg : ∀ α, f (g α) = h α) :
    ((unif.map g).toPMF).map f = (unif.map h).toPMF := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ (hf := measurable_of_finite f), Measure.toPMF_toMeasure,
    Measure.toPMF_toMeasure, Measure.map_map (measurable_of_finite f) hg]
  congr 1
  funext α
  exact hfg α


/-! ### Ceilings of `x - α` for uniform `α` -/

theorem ae_Ico : ∀ᵐ α ∂unif, α ∈ Set.Ico (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ico

theorem ceil_sub_eq (x α : ℝ) (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ⌈x - α⌉ = ⌊x⌋ + if α < Int.fract x then 1 else 0 := by
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have hf : Int.fract x = x - ⌊x⌋ := rfl
  obtain ⟨h0, h1'⟩ := hα
  split_ifs with h
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  · rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith

theorem ceil_ae (x : ℝ) : (fun α : ℝ => ((⌈x - α⌉ : ℤ) : ℝ)) =ᵐ[unif]
    fun α => (⌊x⌋ : ℝ) + (Set.Iio (Int.fract x)).indicator (fun _ => (1 : ℝ)) α := by
  filter_upwards [ae_Ico] with α hα
  rw [ceil_sub_eq x α hα, Set.indicator_apply]
  by_cases h : α < Int.fract x <;> simp [h]

theorem integrable_ceil (x : ℝ) : Integrable (fun α : ℝ => ((⌈x - α⌉ : ℤ) : ℝ)) unif :=
  ((integrable_const _).add ((integrable_const (1 : ℝ)).indicator measurableSet_Iio)).congr
    (ceil_ae x).symm

theorem integral_ceil (x : ℝ) : ∫ α, ((⌈x - α⌉ : ℤ) : ℝ) ∂unif = x := by
  rw [integral_congr_ae (ceil_ae x), integral_add (integrable_const _)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iio), integral_const,
    integral_indicator_const _ measurableSet_Iio]
  have hI : Set.Iio (Int.fract x) ∩ Set.Ico 0 1 = Set.Ico 0 (Int.fract x) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
    have := Int.fract_lt_one x
    constructor
    · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
  rw [probReal_univ, one_smul, smul_eq_mul, mul_one, measureReal_def, unif,
    Measure.restrict_apply measurableSet_Iio, hI, Real.volume_Ico, sub_zero,
    ENNReal.toReal_ofReal (Int.fract_nonneg x)]
  exact Int.floor_add_fract x

theorem integral_abs_ceil_sub (x x' : ℝ) :
    ∫ α, |((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ)| ∂unif = |x' - x| := by
  rcases le_total x x' with h | h
  · have hp : ∀ α : ℝ, |((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ)| =
        ((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ) := fun α => by
      apply abs_of_nonneg
      have : ⌈x - α⌉ ≤ ⌈x' - α⌉ := Int.ceil_mono (by linarith)
      have : ((⌈x - α⌉ : ℤ) : ℝ) ≤ ((⌈x' - α⌉ : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    simp_rw [hp]
    rw [integral_sub (integrable_ceil _) (integrable_ceil _), integral_ceil, integral_ceil,
      abs_of_nonneg (by linarith)]
  · have hp : ∀ α : ℝ, |((⌈x' - α⌉ : ℤ) : ℝ) - ((⌈x - α⌉ : ℤ) : ℝ)| =
        ((⌈x - α⌉ : ℤ) : ℝ) - ((⌈x' - α⌉ : ℤ) : ℝ) := fun α => by
      rw [abs_sub_comm]
      apply abs_of_nonneg
      have : ⌈x' - α⌉ ≤ ⌈x - α⌉ := Int.ceil_mono (by linarith)
      have : ((⌈x' - α⌉ : ℤ) : ℝ) ≤ ((⌈x - α⌉ : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    simp_rw [hp]
    rw [integral_sub (integrable_ceil _) (integrable_ceil _), integral_ceil, integral_ceil,
      abs_sub_comm, abs_of_nonneg (by linarith)]

theorem ceil_sub_bounds (a b α : ℝ) :
    a - b - 1 < (((⌈a - α⌉ - ⌈b - α⌉ : ℤ)) : ℝ) ∧ (((⌈a - α⌉ - ⌈b - α⌉ : ℤ)) : ℝ) < a - b + 1 := by
  have h1 := Int.le_ceil (a - α)
  have h2 := Int.ceil_lt_add_one (a - α)
  have h3 := Int.le_ceil (b - α)
  have h4 := Int.ceil_lt_add_one (b - α)
  push_cast
  constructor <;> linarith

/-! ### Class masses -/

variable (w : Page → ℝ)

/-- The raw count `n_v(α)` (without truncation). -/
def rawN (y : Page → ℝ) (α v : ℝ) : ℤ := ⌈massLE w y v - α⌉ - ⌈massLT w y v - α⌉

theorem massLE_sub_massLT (y : Page → ℝ) (v : ℝ) :
    massLE w y v - massLT w y v = classMass w y v := by
  unfold massLE massLT classMass cls
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases lt_trichotomy (w q) v with h | h | h
  · simp [h, h.le, h.ne]
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']

theorem classMass_nonneg {y : Page → ℝ} (h01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (v : ℝ) :
    0 ≤ classMass w y v := Finset.sum_nonneg fun i _ => (h01 i).1

theorem classMass_le {y : Page → ℝ} (h01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (v : ℝ) :
    classMass w y v ≤ Fintype.card Page := by
  calc classMass w y v ≤ ∑ q ∈ cls w v, (1 : ℝ) := Finset.sum_le_sum fun i _ => (h01 i).2
    _ = (cls w v).card := by simp
    _ ≤ Fintype.card Page := by exact_mod_cast Finset.card_le_univ _

theorem slots_cast {y : Page → ℝ} (h01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (α : ℝ) (v : WClass w) :
    (((slots w y α v : ℕ)) : ℝ) = ((rawN w y α v : ℤ) : ℝ) := by
  have hb := ceil_sub_bounds (massLE w y v) (massLT w y v) α
  rw [massLE_sub_massLT] at hb
  have hm0 := classMass_nonneg w h01 v
  have hmN := classMass_le w h01 v
  have hn0 : 0 ≤ rawN w y α v := by
    have : (-1 : ℝ) < ((rawN w y α v : ℤ) : ℝ) := by unfold rawN; linarith [hb.1]
    have : (-1 : ℤ) < rawN w y α v := by exact_mod_cast this
    omega
  have hnN : rawN w y α v ≤ Fintype.card Page := by
    have : ((rawN w y α v : ℤ) : ℝ) < (Fintype.card Page : ℝ) + 1 := by unfold rawN; linarith [hb.2]
    have : rawN w y α v < (Fintype.card Page : ℤ) + 1 := by exact_mod_cast this
    omega
  have e : ((slots w y α v : ℕ)) = (rawN w y α v).toNat := by
    simp only [slots]
    unfold rawN at hnN hn0 ⊢
    omega
  rw [e]
  have := Int.toNat_of_nonneg hn0
  exact_mod_cast this

/-! ### Telescoping over classes -/

theorem tele (y : Page → ℝ) (α : ℝ) (s : Finset ℝ) :
    (∀ v ∈ Finset.univ.image w, ∀ u ∈ s, v ≤ u → v ∈ s) →
    ∑ v ∈ s, rawN w y α v =
      ⌈(∑ q ∈ Finset.univ.filter (fun q => w q ∈ s), y q) - α⌉ - ⌈(0 : ℝ) - α⌉ := by
  induction s using Finset.induction_on_max with
  | empty => intro _; simp
  | insert a s hlt ih =>
    intro hdc
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hdc' : ∀ v ∈ Finset.univ.image w, ∀ u ∈ s, v ≤ u → v ∈ s := by
      intro v hv u hu hvu
      rcases Finset.mem_insert.mp (hdc v hv u (Finset.mem_insert_of_mem hu) hvu) with h | h
      · subst h; exact absurd hvu (not_le.mpr (hlt u hu))
      · exact h
    rw [Finset.sum_insert ha, ih hdc']
    have hT : ∀ q, w q ∈ Finset.univ.image w := fun q => Finset.mem_image_of_mem w (Finset.mem_univ q)
    have e1 : massLE w y a = ∑ q ∈ Finset.univ.filter (fun q => w q ∈ insert a s), y q := by
      unfold massLE
      congr 1
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases eq_or_lt_of_le h with h' | h'
        · rw [h']; exact Finset.mem_insert_self a s
        · exact hdc (w q) (hT q) a (Finset.mem_insert_self a s) h
      · intro h
        rcases Finset.mem_insert.mp h with h' | h'
        · exact h'.le
        · exact (hlt _ h').le
    have e2 : massLT w y a = ∑ q ∈ Finset.univ.filter (fun q => w q ∈ s), y q := by
      unfold massLT
      congr 1
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        rcases Finset.mem_insert.mp (hdc (w q) (hT q) a (Finset.mem_insert_self a s) h.le)
          with h' | h'
        · exact absurd h' h.ne
        · exact h'
      · exact hlt _
    unfold rawN
    rw [e1, e2]
    ring

theorem sum_rawN {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) : ∑ v : WClass w, rawN w y α v = k := by
  rw [Finset.sum_coe_sort (Finset.univ.image w) (fun v => rawN w y α v)]
  rw [tele w y α _ (fun v hv _ _ _ => hv)]
  have hf : Finset.univ.filter (fun q => w q ∈ Finset.univ.image w) = Finset.univ :=
    Finset.filter_true_of_mem fun q _ => Finset.mem_image_of_mem w (Finset.mem_univ q)
  rw [hf, hy.2]
  obtain ⟨h0, h1⟩ := hα
  have c1 : ⌈(k : ℝ) - α⌉ = k := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  have c2 : ⌈(0 : ℝ) - α⌉ = 0 := by
    rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith
  rw [c1, c2, sub_zero]

theorem card_eq_sum_cls (C : Finset Page) :
    C.card = ∑ v : WClass w, (C ∩ cls w v).card := by
  rw [Finset.sum_coe_sort (Finset.univ.image w) (fun v => (C ∩ cls w v).card),
    Finset.card_eq_sum_card_fiberwise (f := w) (t := Finset.univ.image w)
      (fun q _ => Finset.mem_image_of_mem w (Finset.mem_univ q))]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  ext q
  simp [cls]

/-! ### The weighted movement bound -/

theorem geo (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) (s : Finset ℝ) :
    ∀ u ∈ Finset.univ.image w, (Finset.univ.image w).filter (· < u) = s → ∑ v ∈ s, v ≤ u := by
  induction s using Finset.induction_on_max with
  | empty =>
    intro u hu _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    simpa using (hw i).le
  | insert a s hlt ih =>
    intro u hu hs
    have haT : a ∈ Finset.univ.image w ∧ a < u := by
      have : a ∈ insert a s := Finset.mem_insert_self a s
      rw [← hs] at this
      exact Finset.mem_filter.mp this
    have h2a : 2 * a ≤ u := by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp haT.1
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
      exact hw2 i j haT.2
    have hs' : (Finset.univ.image w).filter (· < a) = s := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hvT, hva⟩
        have : v ∈ (Finset.univ.image w).filter (· < u) :=
          Finset.mem_filter.mpr ⟨hvT, hva.trans haT.2⟩
        rw [hs] at this
        rcases Finset.mem_insert.mp this with h | h
        · exact absurd h hva.ne
        · exact h
      · intro hv
        have : v ∈ insert a s := Finset.mem_insert_of_mem hv
        rw [← hs] at this
        exact ⟨(Finset.mem_filter.mp this).1, hlt v hv⟩
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.sum_insert ha]
    have := ih a haT.1 hs'
    linarith

theorem exch_lt (T : Finset ℝ) (d : Page → ℝ) :
    ∑ v ∈ T, v * ∑ i ∈ Finset.univ.filter (fun i => v < w i), d i =
      ∑ i, d i * ∑ v ∈ T.filter (fun v => v < w i), v := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

theorem exch_le (T : Finset ℝ) (d : Page → ℝ) :
    ∑ v ∈ T, v * ∑ i ∈ Finset.univ.filter (fun i => v ≤ w i), d i =
      ∑ i, d i * ∑ v ∈ T.filter (fun v => v ≤ w i), v := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> ring

theorem abs_massLE_sub {y y' : Page → ℝ} (hs : ∑ i, y' i = ∑ i, y i) (v : ℝ) :
    |massLE w y' v - massLE w y v| ≤
      ∑ i ∈ Finset.univ.filter (fun i => v < w i), |y' i - y i| := by
  have hd : ∑ i, (y' i - y i) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => w i ≤ v)
    (fun i => y' i - y i)
  rw [hd] at hsplit
  have e : massLE w y' v - massLE w y v =
      -∑ i ∈ Finset.univ.filter (fun i => ¬ w i ≤ v), (y' i - y i) := by
    unfold massLE; rw [← Finset.sum_sub_distrib]; linarith
  rw [e, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [Finset.filter_congr (fun i _ => not_le)]

theorem abs_massLT_sub {y y' : Page → ℝ} (hs : ∑ i, y' i = ∑ i, y i) (v : ℝ) :
    |massLT w y' v - massLT w y v| ≤
      ∑ i ∈ Finset.univ.filter (fun i => v ≤ w i), |y' i - y i| := by
  have hd : ∑ i, (y' i - y i) = 0 := by rw [Finset.sum_sub_distrib, hs, sub_self]
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => w i < v)
    (fun i => y' i - y i)
  rw [hd] at hsplit
  have e : massLT w y' v - massLT w y v =
      -∑ i ∈ Finset.univ.filter (fun i => ¬ w i < v), (y' i - y i) := by
    unfold massLT; rw [← Finset.sum_sub_distrib]; linarith
  rw [e, abs_neg]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  rw [Finset.filter_congr (fun i _ => not_lt)]

theorem comb (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j)
    {y y' : Page → ℝ} (hs : ∑ i, y' i = ∑ i, y i) :
    ∑ v : WClass w, (v : ℝ) * (|massLE w y' v - massLE w y v| + |massLT w y' v - massLT w y v|) ≤
      3 * ∑ i, w i * |y' i - y i| := by
  set T := Finset.univ.image w with hT
  rw [Finset.sum_coe_sort T (fun v => v * (|massLE w y' v - massLE w y v| +
    |massLT w y' v - massLT w y v|))]
  calc ∑ v ∈ T, v * (|massLE w y' v - massLE w y v| + |massLT w y' v - massLT w y v|)
      ≤ ∑ v ∈ T, v * (∑ i ∈ Finset.univ.filter (fun i => v < w i), |y' i - y i| +
          ∑ i ∈ Finset.univ.filter (fun i => v ≤ w i), |y' i - y i|) := by
        refine Finset.sum_le_sum fun v hv => ?_
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
        exact mul_le_mul_of_nonneg_left
          (add_le_add (abs_massLE_sub w hs _) (abs_massLT_sub w hs _)) (hw j).le
    _ = ∑ i, |y' i - y i| * (∑ v ∈ T.filter (fun v => v < w i), v +
          ∑ v ∈ T.filter (fun v => v ≤ w i), v) := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [exch_lt, exch_le]
    _ ≤ ∑ i, |y' i - y i| * (3 * w i) := by
        refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        have hwi : w i ∈ T := Finset.mem_image_of_mem w (Finset.mem_univ i)
        have g := geo w hw hw2 _ (w i) hwi rfl
        have hins : T.filter (fun v => v ≤ w i) = insert (w i) (T.filter (fun v => v < w i)) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨h1, h2⟩
            rcases eq_or_lt_of_le h2 with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h1, h⟩
          · rintro (h | ⟨h1, h2⟩)
            · subst h; exact ⟨hwi, le_rfl⟩
            · exact ⟨h1, h2.le⟩
        rw [hins, Finset.sum_insert (by simp)]
        linarith
    _ = 3 * ∑ i, w i * |y' i - y i| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-! ### Integral cache -/

theorem indicator_mem01 (C₀ : Finset Page) : ∀ i, 0 ≤ indicator C₀ i ∧ indicator C₀ i ≤ 1 := by
  intro i; unfold indicator; split_ifs <;> norm_num

theorem sum_indicator (C₀ s : Finset Page) :
    ∑ q ∈ s, indicator C₀ q = ((s ∩ C₀).card : ℝ) := by
  simp [indicator]

theorem ceil_nat_sub (m : ℕ) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) : ⌈(m : ℝ) - α⌉ = m := by
  obtain ⟨h0, h1⟩ := hα
  rw [Int.ceil_eq_iff]; push_cast; constructor <;> linarith

end BBNProof.Profile

namespace BBNProof
variable {Page : Type} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

theorem rhoLaw_fst (y y' : Page → ℝ) : (rhoLaw w y y').map Prod.fst = profLaw w y :=
  Profile.map_toPMF _ ((measurable_slots w y).prodMk (measurable_slots w y')) _ _ fun _ => rfl

theorem rhoLaw_snd (y y' : Page → ℝ) : (rhoLaw w y y').map Prod.snd = profLaw w y' :=
  Profile.map_toPMF _ ((measurable_slots w y).prodMk (measurable_slots w y')) _ _ fun _ => rfl

end BBNProof

namespace BBNProof
variable {Page : Type} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

theorem profLaw_bounds {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) {c : Prof w}
    (hc : c ∈ (profLaw w y).support) (v : WClass w) :
    classMass w y v - 1 < ((c v : ℕ) : ℝ) ∧ ((c v : ℕ) : ℝ) < classMass w y v + 1 := by
  obtain ⟨α, -, rfl⟩ := Profile.exists_of_mem_support _ (measurable_slots w y) hc
  rw [Profile.slots_cast w hy.1, ← Profile.massLE_sub_massLT]
  exact Profile.ceil_sub_bounds _ _ _

theorem card_of_profLaw {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) {c : Prof w}
    (hc : c ∈ (profLaw w y).support) (C : Finset Page) (hC : profile w C = c) : C.card = k := by
  obtain ⟨α, hα, rfl⟩ := Profile.exists_of_mem_support _ (measurable_slots w y) hc
  have h : (C.card : ℝ) = k := by
    rw [Profile.card_eq_sum_cls w C]
    push_cast
    have : ∀ v : WClass w, (((C ∩ cls w v).card : ℕ) : ℝ) = ((Profile.rawN w y α v : ℤ) : ℝ) := by
      intro v
      rw [← Profile.slots_cast w hy.1 α v, ← hC]
      rfl
    simp_rw [this]
    exact_mod_cast Profile.sum_rawN w hy hα
  exact_mod_cast h

theorem profLaw_mean {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k) (v : WClass w) :
    ∑ c, (profLaw w y c).toReal * ((c v : ℕ) : ℝ) = classMass w y v := by
  unfold profLaw
  rw [Profile.sum_toPMF _ (measurable_slots w y) (fun c => ((c v : ℕ) : ℝ))]
  simp_rw [Profile.slots_cast w hy.1, Profile.rawN]
  push_cast
  rw [integral_sub (Profile.integrable_ceil _) (Profile.integrable_ceil _), Profile.integral_ceil,
    Profile.integral_ceil, Profile.massLE_sub_massLT]

theorem rhoLaw_move (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) {k : ℕ}
    {y y' : Page → ℝ} (hy : y ∈ fracCaches k) (hy' : y' ∈ fracCaches k) :
    ∑ x, (rhoLaw w y y' x).toReal *
        ∑ v : WClass w, (v : ℝ) * |((x.2 v : ℕ) : ℝ) - ((x.1 v : ℕ) : ℝ)| ≤
      3 * ∑ i, w i * |y' i - y i| := by
  unfold rhoLaw
  rw [Profile.sum_toPMF _ ((measurable_slots w y).prodMk (measurable_slots w y'))
    (fun x => ∑ v : WClass w, (v : ℝ) * |((x.2 v : ℕ) : ℝ) - ((x.1 v : ℕ) : ℝ)|)]
  simp_rw [Profile.slots_cast w hy.1, Profile.slots_cast w hy'.1, Profile.rawN]
  push_cast
  have ic := Profile.integrable_ceil
  have hpos : ∀ v : WClass w, 0 ≤ (v : ℝ) := fun v => by
    obtain ⟨j, _, h⟩ := Finset.mem_image.mp v.2
    rw [← h]; exact (hw j).le
  calc ∫ α, ∑ v : WClass w, (v : ℝ) *
        |((⌈massLE w y' v - α⌉ : ℤ) : ℝ) - ((⌈massLT w y' v - α⌉ : ℤ) : ℝ) -
          (((⌈massLE w y v - α⌉ : ℤ) : ℝ) - ((⌈massLT w y v - α⌉ : ℤ) : ℝ))| ∂unif
      ≤ ∫ α, ∑ v : WClass w, (v : ℝ) *
        (|((⌈massLE w y' v - α⌉ : ℤ) : ℝ) - ((⌈massLE w y v - α⌉ : ℤ) : ℝ)| +
          |((⌈massLT w y' v - α⌉ : ℤ) : ℝ) - ((⌈massLT w y v - α⌉ : ℤ) : ℝ)|) ∂unif := by
        refine integral_mono
          (integrable_finsetSum _ fun v _ =>
            (((ic _).sub (ic _)).sub ((ic _).sub (ic _))).abs.const_mul _)
          (integrable_finsetSum _ fun v _ =>
            (((ic _).sub (ic _)).abs.add ((ic _).sub (ic _)).abs).const_mul _) fun α => ?_
        refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (hpos v)
        rw [abs_le]
        constructor <;> linarith [le_abs_self (((⌈massLE w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLE w y v - α⌉ : ℤ) : ℝ)), neg_abs_le (((⌈massLE w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLE w y v - α⌉ : ℤ) : ℝ)), le_abs_self (((⌈massLT w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLT w y v - α⌉ : ℤ) : ℝ)), neg_abs_le (((⌈massLT w y' v - α⌉ : ℤ) : ℝ) -
          ((⌈massLT w y v - α⌉ : ℤ) : ℝ))]
    _ = ∑ v : WClass w, (v : ℝ) * (|massLE w y' v - massLE w y v| + |massLT w y' v - massLT w y v|) := by
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun v _ => ?_
          rw [integral_const_mul, integral_add, Profile.integral_abs_ceil_sub,
            Profile.integral_abs_ceil_sub]
          · exact ((ic _).sub (ic _)).abs
          · exact ((ic _).sub (ic _)).abs
        · intro v _
          exact (((ic _).sub (ic _)).abs.add ((ic _).sub (ic _)).abs).const_mul _
    _ ≤ 3 * ∑ i, w i * |y' i - y i| := Profile.comb w hw hw2 (by rw [hy.2, hy'.2])

theorem profLaw_indicator (C₀ : Finset Page) :
    profLaw w (indicator C₀) = PMF.pure (profile w C₀) := by
  unfold profLaw
  apply PMF.toMeasure_injective
  have hae : slots w (indicator C₀) =ᵐ[unif] fun _ => profile w C₀ := by
    filter_upwards [Profile.ae_Ico] with α hα
    funext v
    apply Fin.ext
    have h := Profile.slots_cast w (Profile.indicator_mem01 C₀) α v
    have hm := Profile.massLE_sub_massLT w (indicator C₀) v
    unfold Profile.rawN at h
    unfold massLE at h hm
    unfold massLT at h hm
    unfold classMass at hm
    rw [Profile.sum_indicator, Profile.sum_indicator] at h hm
    rw [Profile.sum_indicator] at hm
    rw [Profile.ceil_nat_sub _ hα, Profile.ceil_nat_sub _ hα] at h
    push_cast at h
    rw [hm, Finset.inter_comm] at h
    exact_mod_cast h
  rw [Measure.toPMF_toMeasure, PMF.toMeasure_pure, Measure.map_congr hae, Measure.map_const,
    measure_univ, one_smul]

end BBNProof
end

/-! ## Inlined from `BBNProof.AddRemove` -/
section

/-!
# Fixing the marginals page by page

Each page `i` independently stays/leaves (if cached) or enters/stays out (if not cached), with
probabilities chosen so that its marginal becomes `y' i`. The kernel is a product of Bernoullis.
-/

noncomputable section
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace BBNProof.AddRemove

variable {Page : Type} [Fintype Page] [DecidableEq Page]

/-- Sum over all sets of a product of per-element choices. -/
theorem sum_prod_ite (f g : Page → ℝ) :
    ∑ C : Finset Page, ∏ i, (if i ∈ C then f i else g i) = ∏ i, (f i + g i) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun C _ => ?_
  have := Finset.prod_piecewise (Finset.univ : Finset Page) C f g
  simp only [Finset.piecewise, Finset.univ_inter] at this
  rw [this, Finset.compl_eq_univ_sdiff]

/-- The probability of `C` under independent inclusions with probabilities `t`. -/
def prodW (t : Page → ℝ) (C : Finset Page) : ℝ := ∏ i, (if i ∈ C then t i else 1 - t i)

theorem prodW_nonneg {t : Page → ℝ} (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (C : Finset Page) :
    0 ≤ prodW t C :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> linarith [ht i]

theorem sum_prodW (t : Page → ℝ) : ∑ C, prodW t C = 1 := by
  unfold prodW; rw [sum_prod_ite]; simp

theorem sum_prodW_mem (t : Page → ℝ) (j : Page) :
    ∑ C, prodW t C * (if j ∈ C then 1 else 0) = t j := by
  have h : ∀ C : Finset Page, prodW t C * (if j ∈ C then 1 else 0) =
      ∏ i, (if i ∈ C then t i else (if i = j then 0 else 1 - t i)) := by
    intro C
    unfold prodW
    by_cases hj : j ∈ C
    · rw [if_pos hj, mul_one]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ C
      · simp [hi]
      · have : i ≠ j := fun h => hi (h ▸ hj)
        simp [hi, this]
    · rw [if_neg hj, mul_zero, eq_comm]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
  simp_rw [h]
  rw [sum_prod_ite]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hij; simp [hij]
  · simp

theorem sum_prodW_affine (t : Page → ℝ) (j : Page) (c d : ℝ) :
    ∑ C, prodW t C * (c + d * (if j ∈ C then 1 else 0)) = c + d * t j := by
  have h : ∀ C, prodW t C * (c + d * (if j ∈ C then 1 else 0)) =
      c * prodW t C + d * (prodW t C * (if j ∈ C then 1 else 0)) := fun C => by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_prodW, sum_prodW_mem, mul_one]

theorem sum_prodW_lin (t : Page → ℝ) (s : Finset Page) (c d : Page → ℝ) :
    ∑ C, prodW t C * ∑ i ∈ s, (c i + d i * (if i ∈ C then 1 else 0)) =
      ∑ i ∈ s, (c i + d i * t i) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_prodW_affine t i (c i) (d i)

/-- The product kernel as a `PMF`. -/
def prodPMF (t : Page → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) : PMF (Finset Page) :=
  PMF.ofFintype (fun C => ENNReal.ofReal (prodW t C)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun C _ => prodW_nonneg ht C), sum_prodW,
      ENNReal.ofReal_one])

theorem prodPMF_toReal (t : Page → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) (C : Finset Page) :
    (prodPMF t ht C).toReal = prodW t C := by
  simp [prodPMF, ENNReal.toReal_ofReal (prodW_nonneg ht C)]

theorem pmf_sum_toReal {α : Type} [Fintype α] (μ : PMF α) : ∑ x, (μ x).toReal = 1 := by
  have h := PMF.tsum_coe μ
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun x _ => PMF.apply_ne_top μ x), h, ENNReal.toReal_one]

variable {w : Page → ℝ}

theorem margX_nonneg (μ : PMF (Finset Page × Prof w)) (i : Page) : 0 ≤ margX μ i :=
  Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

theorem margX_le_one (μ : PMF (Finset Page × Prof w)) (i : Page) : margX μ i ≤ 1 := by
  rw [← pmf_sum_toReal μ]
  refine Finset.sum_le_sum fun x _ => ?_
  have := (μ x).toReal_nonneg
  split_ifs <;> nlinarith

theorem sum_ite_mem (μ : PMF (Finset Page × Prof w)) (i : Page) (c d : ℝ) :
    ∑ x, (μ x).toReal * (if i ∈ x.1 then c else d) = c * margX μ i + d * (1 - margX μ i) := by
  have h : ∀ x : Finset Page × Prof w, (μ x).toReal * (if i ∈ x.1 then c else d) =
      c * ((μ x).toReal * (if i ∈ x.1 then 1 else 0)) + d * (μ x).toReal -
        d * ((μ x).toReal * (if i ∈ x.1 then 1 else 0)) := by
    intro x; split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, pmf_sum_toReal]
  unfold margX; ring

/-- Probability of adding a missing page. -/
def addP (y y' : Page → ℝ) (i : Page) : ℝ := max 0 (y' i - y i) / (1 - y i)

/-- Probability of removing a cached page. -/
def remP (y y' : Page → ℝ) (i : Page) : ℝ := max 0 (y i - y' i) / y i

theorem addP_mul {y y' : Page → ℝ} (_hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : addP y y' i * (1 - y i) = max 0 (y' i - y i) := by
  unfold addP
  by_cases h : 1 - y i = 0
  · rw [h, mul_zero]; have := hy' i; rw [eq_comm, max_eq_left]; linarith
  · field_simp

theorem remP_mul {y y' : Page → ℝ} (_hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : remP y y' i * y i = max 0 (y i - y' i) := by
  unfold remP
  by_cases h : y i = 0
  · rw [h, mul_zero]; have := hy' i; rw [eq_comm, max_eq_left]; linarith
  · field_simp

theorem addP_mem {y y' : Page → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : 0 ≤ addP y y' i ∧ addP y y' i ≤ 1 := by
  have h1 := hy i; have h2 := hy' i
  unfold addP
  refine ⟨div_nonneg (le_max_left _ _) (by linarith), div_le_one_of_le₀ ?_ (by linarith)⟩
  exact max_le (by linarith) (by linarith)

theorem remP_mem {y y' : Page → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1)
    (i : Page) : 0 ≤ remP y y' i ∧ remP y y' i ≤ 1 := by
  have h1 := hy i; have h2 := hy' i
  unfold remP
  refine ⟨div_nonneg (le_max_left _ _) h1.1, div_le_one_of_le₀ ?_ h1.1⟩
  exact max_le h1.1 (by linarith)

/-- The inclusion probability of page `i` after the step, given the old cache `C`. -/
def incl (y y' : Page → ℝ) (C : Finset Page) (i : Page) : ℝ :=
  if i ∈ C then 1 - remP y y' i else addP y y' i

theorem incl_mem {y y' : Page → ℝ} (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1) (C : Finset Page) (i : Page) :
    0 ≤ incl y y' C i ∧ incl y y' C i ≤ 1 := by
  unfold incl
  have := addP_mem hy hy' i; have := remP_mem hy hy' i
  split_ifs <;> constructor <;> linarith

/-- Pointwise shortfall bound. -/
theorem shortfall_le (m : ℝ) (s C C' : Finset Page) :
    max 0 (m - ((C' ∩ s).card : ℝ)) ≤ max 0 (m - ((C ∩ s).card : ℝ)) +
      ∑ i ∈ s, (if i ∈ C then 1 - (if i ∈ C' then 1 else 0) else 0) := by
  have hsum : ∑ i ∈ s, (if i ∈ C then 1 - (if i ∈ C' then (1 : ℝ) else 0) else 0) =
      ((s.filter (fun i => i ∈ C ∧ i ∉ C')).card : ℝ) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : i ∈ C <;> by_cases h2 : i ∈ C' <;> simp [h1, h2]
  have hcard : (C ∩ s).card ≤ (C' ∩ s).card + (s.filter (fun i => i ∈ C ∧ i ∉ C')).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i hi
    rw [Finset.mem_inter] at hi
    by_cases h : i ∈ C'
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨h, hi.2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hi.2, hi.1, h⟩)
  rw [hsum]
  have : ((C ∩ s).card : ℝ) ≤ ((C' ∩ s).card : ℝ) +
      ((s.filter (fun i => i ∈ C ∧ i ∉ C')).card : ℝ) := by exact_mod_cast hcard
  have h0 : (0 : ℝ) ≤ ((s.filter (fun i => i ∈ C ∧ i ∉ C')).card : ℝ) := Nat.cast_nonneg _
  refine max_le (by positivity) ?_
  linarith [le_max_right 0 (m - ((C ∩ s).card : ℝ))]

end BBNProof.AddRemove

namespace BBNProof

open AddRemove

variable {Page : Type} [Fintype Page] [DecidableEq Page]

theorem add_remove (w : Page → ℝ) (hw : ∀ i, 0 ≤ w i) (y' : Page → ℝ)
    (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1) (μ : PMF (Finset Page × Prof w)) :
    ∃ κ : Finset Page × Prof w → PMF (Finset Page),
      (∀ i, ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * (if i ∈ C' then 1 else 0) = y' i) ∧
      (∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * ∑ i ∈ C' \ x.1, w i ≤
        ∑ i, w i * max 0 (y' i - margX μ i)) ∧
      (∀ v : WClass w,
        ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal *
            max 0 (((x.2 v : ℕ) : ℝ) - ((profile w C' v : ℕ) : ℝ)) ≤
          ∑ x, (μ x).toReal * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
            ∑ i ∈ cls w v, max 0 (margX μ i - y' i)) := by
  set y := margX μ with hydef
  have hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := fun i => ⟨margX_nonneg μ i, margX_le_one μ i⟩
  have ht := incl_mem hy hy'
  refine ⟨fun x => prodPMF (incl y y' x.1) (ht x.1), ?_, ?_, ?_⟩
  · -- marginals
    intro i
    simp_rw [prodPMF_toReal, mul_assoc, ← Finset.mul_sum, sum_prodW_mem]
    unfold incl
    rw [sum_ite_mem]
    have h1 := addP_mul hy hy' i; have h2 := remP_mul hy hy' i
    rw [← hydef]
    have : max 0 (y' i - y i) - max 0 (y i - y' i) = y' i - y i := by
      rcases le_total (y' i) (y i) with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    nlinarith
  · -- fetch cost
    apply le_of_eq
    have hpt : ∀ (x : Finset Page × Prof w) (C' : Finset Page), ∑ i ∈ C' \ x.1, w i =
        ∑ i, (if i ∈ x.1 then 0 else w i) * (if i ∈ C' then 1 else 0) := by
      intro x C'
      rw [show (∑ i, (if i ∈ x.1 then 0 else w i) * (if i ∈ C' then (1 : ℝ) else 0)) =
          ∑ i, (if i ∈ C' \ x.1 then w i else 0) from Finset.sum_congr rfl fun i _ => by
            by_cases h1 : i ∈ x.1 <;> by_cases h2 : i ∈ C' <;> simp [h1, h2],
        Finset.sum_ite_mem, Finset.univ_inter]
    have hx : ∀ x : Finset Page × Prof w,
        ∑ C', (μ x).toReal * (prodPMF (incl y y' x.1) (ht x.1) C').toReal * ∑ i ∈ C' \ x.1, w i =
          ∑ i, (μ x).toReal * (if i ∈ x.1 then 0 else w i * addP y y' i) := by
      intro x
      simp_rw [hpt, prodPMF_toReal, mul_assoc, ← Finset.mul_sum]
      have := sum_prodW_lin (incl y y' x.1) Finset.univ (fun _ => 0)
        (fun i => if i ∈ x.1 then 0 else w i)
      simp only [zero_add] at this
      rw [this]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold incl; split_ifs <;> simp
    simp_rw [hx]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_ite_mem, ← hydef, zero_mul, zero_add, mul_assoc, addP_mul hy hy']
  · intro v
    calc _ ≤ ∑ x, ∑ C', (μ x).toReal * (prodPMF (incl y y' x.1) (ht x.1) C').toReal *
            (max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
              ∑ i ∈ cls w v, ((if i ∈ x.1 then 1 else 0) +
                (if i ∈ x.1 then -1 else 0) * (if i ∈ C' then 1 else 0))) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun C' _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h := shortfall_le ((x.2 v : ℕ) : ℝ) (cls w v) x.1 C'
          have he : ∀ i, (if i ∈ x.1 then 1 - (if i ∈ C' then (1 : ℝ) else 0) else 0) =
              (if i ∈ x.1 then 1 else 0) + (if i ∈ x.1 then -1 else 0) *
                (if i ∈ C' then 1 else 0) := fun i => by split_ifs <;> ring
          simp_rw [he] at h
          exact h
      _ = ∑ x, (μ x).toReal * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
            ∑ x, ∑ i ∈ cls w v, (μ x).toReal * (if i ∈ x.1 then remP y y' i else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp_rw [prodPMF_toReal, mul_assoc, ← Finset.mul_sum]
          rw [← mul_add]
          congr 1
          rw [Finset.sum_congr rfl (fun C _ => mul_add _ _ _), Finset.sum_add_distrib,
            ← Finset.sum_mul, sum_prodW, one_mul, sum_prodW_lin]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          unfold incl; split_ifs <;> ring
      _ = _ := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [sum_ite_mem, ← hydef, zero_mul, add_zero, remP_mul hy hy']

end BBNProof
end

/-! ## Inlined from `BBNProof.Transfer` -/
section

/-!
# Hole/excess transfers within each weight class (BBN)

Proof of `BBNProof.transfer`. The state is a pair `((C, m), D)` of the initial cache `C`, the target
profile `m`, and the current cache `D`. A *round* for a class `v` moves one page of class `v` from
caches with an excess in `v` to caches with a hole in `v` (product coupling), preserving the
marginals. Each round decreases `∑ᵥ (max excess + max hole)` over the support, so finitely many
rounds reach the target profile.
-/

noncomputable section
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace BBNProof

namespace Transfer

/-! ### Expectations over finite PMFs -/

section Expect

variable {α β : Type} [Fintype α] [Fintype β]

/-- The expectation of `f` under `p`. -/
def ex (p : PMF α) (f : α → ℝ) : ℝ := ∑ a, (p a).toReal * f a

lemma toReal_bind (p : PMF α) (k : α → PMF β) (b : β) :
    ((p.bind k) b).toReal = ∑ a, (p a).toReal * (k a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

lemma ex_bind (p : PMF α) (k : α → PMF β) (f : β → ℝ) :
    ex (p.bind k) f = ex p (fun a => ex (k a) f) := by
  unfold ex
  simp_rw [toReal_bind, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

lemma ex_pure [DecidableEq α] (a : α) (f : α → ℝ) : ex (PMF.pure a) f = f a := by
  simp only [ex, PMF.pure_apply]
  simp [apply_ite ENNReal.toReal, ite_mul]

lemma ex_map (p : PMF α) (h : α → β) (f : β → ℝ) : ex (p.map h) f = ex p (f ∘ h) := by
  classical
  rw [← PMF.bind_pure_comp, ex_bind]
  simp [ex_pure]
  rfl

lemma toReal_ne_zero {p : PMF α} {a : α} : (p a).toReal ≠ 0 ↔ p a ≠ 0 := by
  rw [Ne, ENNReal.toReal_eq_zero_iff]
  simp [PMF.apply_ne_top]

lemma toReal_pos {p : PMF α} {a : α} (h : p a ≠ 0) : 0 < (p a).toReal :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm (toReal_ne_zero.2 h))

/-- One step: with probability `r z` move to `g z`, otherwise stay at `b₀`. -/
def stepK {Z : Type} [Fintype Z] (r : Z → ℝ) (g : Z → β) (b₀ : β) : PMF β :=
  if h : (∀ z, 0 ≤ r z) ∧ ∑ z, r z ≤ 1 then
    (PMF.ofFintype (fun o : Option Z => ENNReal.ofReal (o.elim (1 - ∑ z, r z) r)) (by
      rw [Fintype.sum_option]
      simp only [Option.elim]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => h.1 z),
        ← ENNReal.ofReal_add (by linarith [h.2]) (Finset.sum_nonneg fun z _ => h.1 z)]
      simp)).map (fun o => o.elim b₀ g)
  else PMF.pure b₀

variable {Z : Type} [Fintype Z]

lemma ex_stepK (r : Z → ℝ) (g : Z → β) (b₀ : β) (h0 : ∀ z, 0 ≤ r z) (h1 : ∑ z, r z ≤ 1)
    (f : β → ℝ) : ex (stepK r g b₀) f = f b₀ + ∑ z, r z * (f (g z) - f b₀) := by
  rw [stepK, dif_pos ⟨h0, h1⟩, ex_map]
  unfold ex
  rw [Fintype.sum_option]
  simp only [PMF.ofFintype_apply, Option.elim, Function.comp]
  rw [ENNReal.toReal_ofReal (by linarith)]
  simp_rw [ENNReal.toReal_ofReal (h0 _)]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

lemma mem_support_stepK (r : Z → ℝ) (g : Z → β) (b₀ : β) (h0 : ∀ z, 0 ≤ r z)
    (h1 : ∑ z, r z ≤ 1) {b : β} (hb : b ∈ (stepK r g b₀).support) :
    (b = b₀ ∧ ∑ z, r z < 1) ∨ ∃ z, r z ≠ 0 ∧ b = g z := by
  rw [stepK, dif_pos ⟨h0, h1⟩, PMF.mem_support_map_iff] at hb
  obtain ⟨o, ho, rfl⟩ := hb
  rw [PMF.mem_support_ofFintype_iff, Ne, ENNReal.ofReal_eq_zero, not_le] at ho
  cases o with
  | none => exact Or.inl ⟨rfl, by simp only [Option.elim] at ho; linarith⟩
  | some z => exact Or.inr ⟨z, ne_of_gt ho, rfl⟩

lemma map_stepK {γ : Type} (r : Z → ℝ) (g : Z → β) (b₀ : β) (h : β → γ) (c : γ)
    (hg : ∀ z, h (g z) = c) (hb : h b₀ = c) : (stepK r g b₀).map h = PMF.pure c := by
  unfold stepK
  split_ifs
  · rw [PMF.map_comp]
    have : (h ∘ fun o : Option Z => o.elim b₀ g) = Function.const _ c := by
      funext o; cases o <;> simp [hg, hb]
    rw [this, PMF.map_const]
  · rw [PMF.pure_map, hb]

end Expect

/-! ### Conditional distributions (copied from `PagingWithDelay.Rounding`) -/

section Cond

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

omit [DecidableEq α] in
lemma map_fst_apply (π : PMF (α × β)) (a : α) : π.map Prod.fst a = ∑ b, π (a, b) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- The conditional distribution of the second coordinate given the first. -/
def condSnd (π : PMF (α × β)) (a : α) : PMF β :=
  if h : π.map Prod.fst a = 0 then π.map Prod.snd else
    PMF.ofFintype (fun b => π (a, b) / π.map Prod.fst a) (by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← map_fst_apply]
      exact ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _))

lemma bind_condSnd (π : PMF (α × β)) :
    (π.map Prod.fst).bind (fun a => (condSnd π a).map (Prod.mk a)) = π := by
  ext ⟨a, b⟩
  have hrow : ∀ a' b', π (a', b') ≤ π.map Prod.fst a' := fun a' b' => by
    rw [map_fst_apply]
    exact Finset.single_le_sum (f := fun b => π (a', b)) (fun _ _ => zero_le)
      (Finset.mem_univ b')
  have hmk : ∀ a' (p : PMF β), p.map (Prod.mk a') (a, b) = if a = a' then p b else 0 := by
    intro a' p
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Ne.symm hb']
    · simp
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single a]
  · rw [hmk, if_pos rfl]
    unfold condSnd
    split_ifs with h
    · simpa [h] using (le_antisymm (h ▸ hrow a b) (zero_le)).symm
    · rw [PMF.ofFintype_apply]
      exact ENNReal.mul_div_cancel h (PMF.apply_ne_top _ _)
  · intro a' _ ha'
    rw [hmk, if_neg (Ne.symm ha'), mul_zero]
  · simp

lemma condSnd_ne_zero {π : PMF (α × β)} {a : α} {b : β} (ha : π.map Prod.fst a ≠ 0)
    (hb : condSnd π a b ≠ 0) : π (a, b) ≠ 0 := by
  unfold condSnd at hb
  rw [dif_neg ha, PMF.ofFintype_apply] at hb
  intro h
  rw [h, ENNReal.zero_div] at hb
  exact hb rfl

lemma ex_cond (π : PMF (α × β)) (μ : PMF α) (h : π.map Prod.fst = μ) (f : α × β → ℝ) :
    ∑ a, ∑ b, (μ a).toReal * (condSnd π a b).toReal * f (a, b) = ex π f := by
  have e : ex π f = ex ((π.map Prod.fst).bind (fun a => (condSnd π a).map (Prod.mk a))) f := by
    rw [bind_condSnd]
  rw [e, ex_bind, h]
  simp only [ex_map]
  unfold ex
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Function.comp, mul_assoc]

end Cond

/-! ### States, counts and the round -/

section Round

variable {Page : Type} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

/-- States: `((initial cache, target profile), current cache)`. -/
abbrev St := (Finset Page × Prof w) × Finset Page

/-- The indicator of a cache. -/
def ind (D : Finset Page) (i : Page) : ℝ := if i ∈ D then 1 else 0

/-- The number of pages of class `v` in the current cache. -/
def cnt (v : WClass w) (z : St w) : ℕ := (z.2 ∩ cls w v).card

/-- The target number of pages of class `v`. -/
def tg (v : WClass w) (z : St w) : ℕ := (z.1.2 v : ℕ)

/-- Some page of class `v` lies in `e` but not in `h`. -/
def Ex (v : WClass w) (h e : St w) : Prop := ∃ p, p ∈ e.2 ∧ p ∉ h.2 ∧ w p = v

open Classical in
/-- The cache of `e` after giving a page of class `v` to `h`. -/
def remC (v : WClass w) (h e : St w) : Finset Page :=
  if hx : Ex w v h e then e.2.erase hx.choose else e.2

open Classical in
/-- The cache of `h` after receiving a page of class `v` from `e`. -/
def addC (v : WClass w) (h e : St w) : Finset Page :=
  if hx : Ex w v h e then insert hx.choose h.2 else h.2

open Classical in
/-- Whether `i` is the page moved from `e` to `h`. -/
def qi (v : WClass w) (h e : St w) (i : Page) : ℝ :=
  if hx : Ex w v h e then (if i = hx.choose then 1 else 0) else 0

lemma mem_cls {p : Page} {u : ℝ} : p ∈ cls w u ↔ w p = u := by simp [cls]

lemma cls_eq {p : Page} {u v : WClass w} (hu : p ∈ cls w u) (hv : w p = v) : u = v :=
  Subtype.ext (((mem_cls w).1 hu).symm.trans hv)

lemma class_nonneg (hw : ∀ i, 0 ≤ w i) (u : WClass w) : 0 ≤ (u : ℝ) := by
  obtain ⟨a, _, ha⟩ := Finset.mem_image.1 u.2
  rw [← ha]; exact hw a

lemma ind_remC (v : WClass w) (h e : St w) (i : Page) :
    ind (remC w v h e) i = ind e.2 i - qi w v h e i := by
  unfold remC qi
  by_cases hx : Ex w v h e
  · rw [dif_pos hx, dif_pos hx]
    by_cases hi : i = hx.choose
    · rw [if_pos hi]; simp [ind, hi, hx.choose_spec.1]
    · rw [if_neg hi]; simp [ind, Finset.mem_erase, hi]
  · rw [dif_neg hx, dif_neg hx]; simp

lemma ind_addC (v : WClass w) (h e : St w) (i : Page) :
    ind (addC w v h e) i = ind h.2 i + qi w v h e i := by
  unfold addC qi
  by_cases hx : Ex w v h e
  · rw [dif_pos hx, dif_pos hx]
    by_cases hi : i = hx.choose
    · rw [if_pos hi]; simp [ind, hi, hx.choose_spec.2.1]
    · rw [if_neg hi]; simp [ind, Finset.mem_insert, hi]
  · rw [dif_neg hx, dif_neg hx]; simp

lemma card_erase_inter (D S : Finset Page) (p : Page) (hp : p ∈ D) :
    ((D.erase p) ∩ S).card + (if p ∈ S then 1 else 0) = (D ∩ S).card := by
  rw [Finset.erase_inter]
  split_ifs with hs
  · have hm : p ∈ D ∩ S := Finset.mem_inter.2 ⟨hp, hs⟩
    rw [Finset.card_erase_of_mem hm]
    have := Finset.card_pos.2 ⟨p, hm⟩
    omega
  · rw [Finset.erase_eq_of_notMem (by simp [hs])]; rfl

lemma card_insert_inter (D S : Finset Page) (p : Page) (hp : p ∉ D) :
    ((insert p D) ∩ S).card = (D ∩ S).card + (if p ∈ S then 1 else 0) := by
  split_ifs with hs
  · rw [Finset.insert_inter_of_mem hs, Finset.card_insert_of_notMem (by simp [hp])]
  · rw [Finset.insert_inter_of_notMem hs]; rfl

/-- If `e` has an excess and `h` a hole in class `v`, and both targets are within `1` of `K v`,
some page of class `v` lies in `e` but not in `h`. -/
lemma ex_of (K : WClass w → ℝ) {v : WClass w} {e h : St w} (hbe : K v - 1 < (tg w v e : ℝ))
    (hbh : (tg w v h : ℝ) < K v + 1) (he : tg w v e < cnt w v e) (hh : cnt w v h < tg w v h) :
    Ex w v h e := by
  have h1 : (tg w v e : ℝ) + 1 ≤ cnt w v e := by exact_mod_cast he
  have h2 : (cnt w v h : ℝ) + 1 ≤ tg w v h := by exact_mod_cast hh
  have h3 : cnt w v h < cnt w v e := by
    have : (cnt w v h : ℝ) < cnt w v e := by linarith
    exact_mod_cast this
  by_contra hne
  apply absurd h3
  apply not_lt.2
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_inter] at hp ⊢
  refine ⟨?_, hp.2⟩
  by_contra hq
  exact hne ⟨p, hp.1, hq, (mem_cls w).1 hp.2⟩

variable (ν : PMF (St w)) (v : WClass w)

/-- The probability of an excess in class `v`. -/
def PE : ℝ := ∑ z, if tg w v z < cnt w v z then (ν z).toReal else 0

/-- The probability of a hole in class `v`. -/
def PH : ℝ := ∑ z, if cnt w v z < tg w v z then (ν z).toReal else 0

/-- `max (PE, PH)`. -/
def MM : ℝ := max (PE w ν v) (PH w ν v)

/-- The rate at which `z` is paired with `z₂`. -/
def rr (z z₂ : St w) : ℝ :=
  if (tg w v z < cnt w v z ∧ cnt w v z₂ < tg w v z₂) ∨
      (cnt w v z < tg w v z ∧ tg w v z₂ < cnt w v z₂) then (ν z₂).toReal / MM w ν v else 0

/-- The state of `z` after being paired with `z₂`. -/
def gg (z z₂ : St w) : St w :=
  if tg w v z < cnt w v z then (z.1, remC w v z₂ z) else (z.1, addC w v z z₂)

/-- One round for class `v`. -/
def round : PMF (St w) := ν.bind (fun z => stepK (rr w ν v z) (gg w v z) z)

variable {w ν v}

lemma rr_nonneg (hM : 0 < MM w ν v) (z z₂ : St w) : 0 ≤ rr w ν v z z₂ := by
  unfold rr; split_ifs
  · exact div_nonneg ENNReal.toReal_nonneg hM.le
  · exact le_rfl

lemma sum_rr (z : St w) : ∑ z₂, rr w ν v z z₂ =
    (if tg w v z < cnt w v z then PH w ν v else if cnt w v z < tg w v z then PE w ν v else 0) /
      MM w ν v := by
  unfold rr PE PH
  by_cases h1 : tg w v z < cnt w v z
  · have h2 : ¬ cnt w v z < tg w v z := by omega
    simp only [h1, h2, true_and, false_and, or_false, ↓reduceIte]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z₂ _ => ?_
    split_ifs <;> simp
  · by_cases h2 : cnt w v z < tg w v z
    · simp only [h1, h2, true_and, false_and, false_or, ↓reduceIte]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun z₂ _ => ?_
      split_ifs <;> simp
    · simp [h1, h2]

lemma sum_rr_le (hM : 0 < MM w ν v) (z : St w) : ∑ z₂, rr w ν v z z₂ ≤ 1 := by
  rw [sum_rr]
  apply div_le_one_of_le₀ _ hM.le
  unfold MM
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _
  · exact hM.le

lemma ex_round (hM : 0 < MM w ν v) (f : St w → ℝ) :
    ex (round w ν v) f = ex ν f +
      ∑ z, ∑ z₂, (ν z).toReal * rr w ν v z z₂ * (f (gg w v z z₂) - f z) := by
  rw [round, ex_bind]
  have hK : ∀ z, ex (stepK (rr w ν v z) (gg w v z) z) f =
      f z + ∑ z₂, rr w ν v z z₂ * (f (gg w v z z₂) - f z) := fun z =>
    ex_stepK _ _ _ (rr_nonneg hM z) (sum_rr_le hM z) f
  simp only [hK]
  simp only [ex, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

lemma pair_cancel {Z : Type} [Fintype Z] (T A : Z → Z → ℝ)
    (h : ∀ z z₂, T z z₂ = A z₂ z - A z z₂) : ∑ z, ∑ z₂, T z z₂ = 0 := by
  simp_rw [h, Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  simp

lemma round_marg (hM : 0 < MM w ν v) (i : Page) :
    ex (round w ν v) (fun z => ind z.2 i) = ex ν (fun z => ind z.2 i) := by
  rw [ex_round hM]
  suffices hs : ∑ z, ∑ z₂, (ν z).toReal * rr w ν v z z₂ *
      (ind (gg w v z z₂).2 i - ind z.2 i) = 0 by rw [hs, add_zero]
  apply pair_cancel _ (fun e h => if tg w v e < cnt w v e ∧ cnt w v h < tg w v h then
    (ν e).toReal * ((ν h).toReal / MM w ν v) * qi w v h e i else 0)
  intro z z₂
  simp only [rr, gg]
  by_cases h1 : tg w v z < cnt w v z <;> by_cases h2 : cnt w v z₂ < tg w v z₂ <;>
    by_cases h3 : cnt w v z < tg w v z <;> by_cases h4 : tg w v z₂ < cnt w v z₂ <;>
    first | omega | (simp only [h1, h2, h3, h4, and_true, and_false,
      or_false, false_or, ↓reduceIte, ind_remC, ind_addC]; ring)

lemma round_map_fst : (round w ν v).map Prod.fst = ν.map Prod.fst := by
  rw [round, PMF.map_bind]
  have : ∀ z, (stepK (rr w ν v z) (gg w v z) z).map Prod.fst = PMF.pure z.1 := fun z =>
    map_stepK _ _ _ _ _ (fun z₂ => by unfold gg; split_ifs <;> rfl) rfl
  simp only [this]
  rfl

end Round


/-! ### Cost, successors and the potential -/

section Main

variable {Page : Type} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

/-- The weight fetched so far plus the weight of the remaining holes. -/
def F (z : St w) : ℝ :=
  ∑ i ∈ z.2 \ z.1.1, w i + ∑ u : WClass w, (u : ℝ) * max 0 ((tg w u z : ℝ) - cnt w u z)

/-- The weight of the initial holes. -/
def G (x : Finset Page × Prof w) : ℝ :=
  ∑ u : WClass w, (u : ℝ) * max 0 (((x.2 u : ℕ) : ℝ) - ((profile w x.1 u : ℕ) : ℝ))

open Classical in
/-- The support as a finset. -/
def suppF (ν : PMF (St w)) : Finset (St w) := Finset.univ.filter (fun z => ν z ≠ 0)

/-- The largest excess in class `u` over the support. -/
def mS (ν : PMF (St w)) (u : WClass w) : ℕ := (suppF w ν).sup (fun z => cnt w u z - tg w u z)

/-- The largest hole in class `u` over the support. -/
def mD (ν : PMF (St w)) (u : WClass w) : ℕ := (suppF w ν).sup (fun z => tg w u z - cnt w u z)

/-- The potential. -/
def Φ (ν : PMF (St w)) : ℕ := ∑ u, (mS w ν u + mD w ν u)

/-- The invariant of the rounds. -/
def Inv (μ : PMF (Finset Page × Prof w)) (y' : Page → ℝ) (ν : PMF (St w)) : Prop :=
  ν.map Prod.fst = μ ∧ (∀ i, ex ν (fun z => ind z.2 i) = y' i) ∧
    (∀ z, ν z ≠ 0 → F w z ≤ G w z.1)

variable {w}

lemma mem_suppF {ν : PMF (St w)} {z : St w} : z ∈ suppF w ν ↔ ν z ≠ 0 := by simp [suppF]

lemma max_aux {a b : ℝ} (h : b + 1 ≤ a) (u : ℝ) :
    u * max 0 (a - (b + 1)) + u = u * max 0 (a - b) := by
  have h1 : max 0 (a - (b + 1)) = a - (b + 1) := max_eq_right (by linarith)
  have h2 : max 0 (a - b) = a - b := max_eq_right (by linarith)
  rw [h1, h2]; ring

lemma F_rem (hw : ∀ i, 0 ≤ w i) {v : WClass w} {z : St w} {p : Page} (hp : p ∈ z.2)
    (hpv : w p = v) (hex : tg w v z < cnt w v z) : F w (z.1, z.2.erase p) ≤ F w z := by
  unfold F
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_erase] at hi ⊢
      exact ⟨hi.1.2, hi.2⟩
    · intro i _ _; exact hw i
  · apply Finset.sum_le_sum
    intro u _
    apply mul_le_mul_of_nonneg_left _ (class_nonneg w hw u)
    have hc := card_erase_inter z.2 (cls w u) p hp
    show max 0 ((tg w u z : ℝ) - (((z.2.erase p) ∩ cls w u).card : ℕ)) ≤
      max 0 ((tg w u z : ℝ) - ((z.2 ∩ cls w u).card : ℕ))
    by_cases hu : p ∈ cls w u
    · have huv : u = v := cls_eq w hu hpv
      subst huv
      rw [if_pos hu] at hc
      unfold cnt at hex
      have h1 : tg w u z ≤ ((z.2.erase p) ∩ cls w u).card := by omega
      have h2 : (tg w u z : ℝ) ≤ (((z.2.erase p) ∩ cls w u).card : ℕ) := by exact_mod_cast h1
      exact (max_le le_rfl (by linarith)).trans (le_max_left _ _)
    · rw [if_neg hu, add_zero] at hc
      rw [hc]

lemma F_add (hw : ∀ i, 0 ≤ w i) {v : WClass w} {z : St w} {p : Page} (hp : p ∉ z.2)
    (hpv : w p = v) (hh : cnt w v z < tg w v z) : F w (z.1, insert p z.2) ≤ F w z := by
  unfold F
  have h1 : ∑ i ∈ insert p z.2 \ z.1.1, w i ≤ w p + ∑ i ∈ z.2 \ z.1.1, w i := by
    calc ∑ i ∈ insert p z.2 \ z.1.1, w i ≤ ∑ i ∈ insert p (z.2 \ z.1.1), w i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            simp only [Finset.mem_sdiff, Finset.mem_insert] at hi ⊢
            tauto
          · intro i _ _; exact hw i
      _ = w p + ∑ i ∈ z.2 \ z.1.1, w i := Finset.sum_insert (by simp [hp])
  have h2 : ∀ u : WClass w, (u : ℝ) * max 0 ((tg w u (z.1, insert p z.2) : ℝ) -
      cnt w u (z.1, insert p z.2)) + (if u = v then (v : ℝ) else 0) ≤
      (u : ℝ) * max 0 ((tg w u z : ℝ) - cnt w u z) := by
    intro u
    have hc := card_insert_inter z.2 (cls w u) p hp
    show (u : ℝ) * max 0 ((tg w u z : ℝ) - (((insert p z.2) ∩ cls w u).card : ℕ)) +
      (if u = v then (v : ℝ) else 0) ≤ (u : ℝ) * max 0 ((tg w u z : ℝ) - ((z.2 ∩ cls w u).card : ℕ))
    by_cases hu : u = v
    · subst hu
      rw [if_pos rfl, hc, if_pos ((mem_cls w).2 hpv)]
      unfold cnt at hh
      have : (((z.2 ∩ cls w u).card : ℕ) : ℝ) + 1 ≤ tg w u z := by exact_mod_cast hh
      push_cast
      exact (max_aux this _).le
    · rw [if_neg hu, hc, if_neg (fun h => hu (cls_eq w h hpv)), add_zero, add_zero]
  have h3 := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset (WClass w))) => h2 u)
  rw [Finset.sum_add_distrib] at h3
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h3
  rw [← hpv] at h3
  linarith

lemma succ (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) {z z' : St w} (hz : ν z ≠ 0)
    (hz' : z' ∈ (stepK (rr w ν v z) (gg w v z) z).support) :
    z'.1 = z.1 ∧ F w z' ≤ F w z ∧ (∀ u, u ≠ v → cnt w u z' = cnt w u z) ∧
    ((z' = z ∧ (tg w v z < cnt w v z → PH w ν v < MM w ν v) ∧
        (cnt w v z < tg w v z → PE w ν v < MM w ν v)) ∨
      (tg w v z < cnt w v z ∧ cnt w v z' + 1 = cnt w v z) ∨
      (cnt w v z < tg w v z ∧ cnt w v z' = cnt w v z + 1)) := by
  rcases mem_support_stepK _ _ _ (rr_nonneg hM z) (sum_rr_le hM z) hz' with
    ⟨rfl, hlt⟩ | ⟨z₂, hr, rfl⟩
  · refine ⟨rfl, le_rfl, fun _ _ => rfl, Or.inl ⟨rfl, fun h => ?_, fun h => ?_⟩⟩
    · rw [sum_rr, if_pos h, div_lt_one hM] at hlt; exact hlt
    · rw [sum_rr, if_neg (by omega), if_pos h, div_lt_one hM] at hlt; exact hlt
  · have hc : ((tg w v z < cnt w v z ∧ cnt w v z₂ < tg w v z₂) ∨
        (cnt w v z < tg w v z ∧ tg w v z₂ < cnt w v z₂)) ∧ ν z₂ ≠ 0 := by
      unfold rr at hr
      split_ifs at hr with hc
      · refine ⟨hc, fun h0 => hr ?_⟩
        simp [h0]
      · exact absurd rfl hr
    obtain ⟨hc, hz₂⟩ := hc
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx : Ex w v z₂ z := ex_of w K (hB z hz v).1 (hB z₂ hz₂ v).2 h1 h2
      have hg : gg w v z z₂ = (z.1, z.2.erase hx.choose) := by
        unfold gg remC; rw [if_pos h1, dif_pos hx]
      obtain ⟨hp1, -, hp3⟩ := hx.choose_spec
      rw [hg]
      refine ⟨rfl, F_rem hw hp1 hp3 h1, fun u hu => ?_, Or.inr (Or.inl ⟨h1, ?_⟩)⟩
      · have hc := card_erase_inter z.2 (cls w u) _ hp1
        rw [if_neg (fun h => hu (cls_eq w h hp3)), add_zero] at hc
        exact hc
      · have hc := card_erase_inter z.2 (cls w v) _ hp1
        rw [if_pos ((mem_cls w).2 hp3)] at hc
        exact hc
    · have hx : Ex w v z z₂ := ex_of w K (hB z₂ hz₂ v).1 (hB z hz v).2 h2 h1
      have hg : gg w v z z₂ = (z.1, insert hx.choose z.2) := by
        unfold gg addC; rw [if_neg (show ¬ tg w v z < cnt w v z by omega), dif_pos hx]
      obtain ⟨-, hp2, hp3⟩ := hx.choose_spec
      rw [hg]
      refine ⟨rfl, F_add hw hp2 hp3 h1, fun u hu => ?_, Or.inr (Or.inr ⟨h1, ?_⟩)⟩
      · have hc := card_insert_inter z.2 (cls w u) _ hp2
        rw [if_neg (fun h => hu (cls_eq w h hp3)), add_zero] at hc
        exact hc
      · have hc := card_insert_inter z.2 (cls w v) _ hp2
        rw [if_pos ((mem_cls w).2 hp3)] at hc
        exact hc

lemma round_supp {ν : PMF (St w)} {v : WClass w} {z' : St w} (h : round w ν v z' ≠ 0) :
    ∃ z, ν z ≠ 0 ∧ z' ∈ (stepK (rr w ν v z) (gg w v z) z).support := by
  have : z' ∈ (round w ν v).support := (PMF.mem_support_iff _ _).2 h
  rw [round, PMF.mem_support_bind_iff] at this
  obtain ⟨z, hz, hz'⟩ := this
  exact ⟨z, (PMF.mem_support_iff _ _).1 hz, hz'⟩

lemma succ_facts (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) {z' : St w} (hz' : round w ν v z' ≠ 0) :
    ∃ z, ν z ≠ 0 ∧ F w z' ≤ F w z ∧ z'.1 = z.1 ∧ (∀ u, tg w u z' = tg w u z) ∧
      (∀ u, u ≠ v → cnt w u z' = cnt w u z) ∧
      ((z' = z ∧ (tg w v z < cnt w v z → PH w ν v < MM w ν v) ∧
          (cnt w v z < tg w v z → PE w ν v < MM w ν v)) ∨
        (tg w v z < cnt w v z ∧ cnt w v z' + 1 = cnt w v z) ∨
        (cnt w v z < tg w v z ∧ cnt w v z' = cnt w v z + 1)) := by
  obtain ⟨z, hz, hz''⟩ := round_supp hz'
  obtain ⟨h1, hF, hc, hcase⟩ := succ hw K hB hM hz hz''
  exact ⟨z, hz, hF, h1, fun u => by unfold tg; rw [h1], hc, hcase⟩

lemma Φ_lt (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) (hE : ∃ z, ν z ≠ 0 ∧ tg w v z < cnt w v z)
    (hH : ∃ z, ν z ≠ 0 ∧ cnt w v z < tg w v z) : Φ w (round w ν v) < Φ w ν := by
  have hle : ∀ u, mS w (round w ν v) u ≤ mS w ν u ∧ mD w (round w ν v) u ≤ mD w ν u := by
    intro u
    constructor
    · apply Finset.sup_le
      intro z' hz'
      obtain ⟨z, hz, -, -, htg, hcnt, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
      have hle : cnt w u z - tg w u z ≤ mS w ν u :=
        Finset.le_sup (f := fun z => cnt w u z - tg w u z) ((mem_suppF).2 hz)
      show cnt w u z' - tg w u z' ≤ mS w ν u
      rw [htg u]
      by_cases hu : u = v
      · subst hu
        rcases hcase with ⟨rfl, -, -⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩ <;> omega
      · rw [hcnt u hu]; exact hle
    · apply Finset.sup_le
      intro z' hz'
      obtain ⟨z, hz, -, -, htg, hcnt, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
      have hle : tg w u z - cnt w u z ≤ mD w ν u :=
        Finset.le_sup (f := fun z => tg w u z - cnt w u z) ((mem_suppF).2 hz)
      show tg w u z' - cnt w u z' ≤ mD w ν u
      rw [htg u]
      by_cases hu : u = v
      · subst hu
        rcases hcase with ⟨rfl, -, -⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩ <;> omega
      · rw [hcnt u hu]; exact hle
  have hlt : mS w (round w ν v) v + mD w (round w ν v) v < mS w ν v + mD w ν v := by
    obtain ⟨z₁, hz₁, he₁⟩ := hE
    obtain ⟨z₂, hz₂, hh₂⟩ := hH
    have hS1 : cnt w v z₁ - tg w v z₁ ≤ mS w ν v :=
      Finset.le_sup (f := fun z => cnt w v z - tg w v z) ((mem_suppF).2 hz₁)
    have hD1 : tg w v z₂ - cnt w v z₂ ≤ mD w ν v :=
      Finset.le_sup (f := fun z => tg w v z - cnt w v z) ((mem_suppF).2 hz₂)
    have h1 := hle v
    rcases le_or_gt (PE w ν v) (PH w ν v) with hP | hP
    · have hMM : MM w ν v = PH w ν v := max_eq_right hP
      have hS : mS w (round w ν v) v ≤ mS w ν v - 1 := by
        apply Finset.sup_le
        intro z' hz'
        obtain ⟨z, hz, -, -, htg, -, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
        have hle : cnt w v z - tg w v z ≤ mS w ν v :=
          Finset.le_sup (f := fun z => cnt w v z - tg w v z) ((mem_suppF).2 hz)
        show cnt w v z' - tg w v z' ≤ mS w ν v - 1
        rw [htg v]
        rcases hcase with ⟨heq, hA, -⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩
        · rw [heq]
          have : ¬ tg w v z < cnt w v z := fun h => lt_irrefl _ (hMM ▸ hA h)
          omega
        · omega
        · omega
      omega
    · have hMM : MM w ν v = PE w ν v := max_eq_left hP.le
      have hD : mD w (round w ν v) v ≤ mD w ν v - 1 := by
        apply Finset.sup_le
        intro z' hz'
        obtain ⟨z, hz, -, -, htg, -, hcase⟩ := succ_facts hw K hB hM ((mem_suppF).1 hz')
        have hle : tg w v z - cnt w v z ≤ mD w ν v :=
          Finset.le_sup (f := fun z => tg w v z - cnt w v z) ((mem_suppF).2 hz)
        show tg w v z' - cnt w v z' ≤ mD w ν v - 1
        rw [htg v]
        rcases hcase with ⟨heq, -, hA⟩ | ⟨hc1, hc⟩ | ⟨hc1, hc⟩
        · rw [heq]
          have : ¬ cnt w v z < tg w v z := fun h => lt_irrefl _ (hMM ▸ hA h)
          omega
        · omega
        · omega
      omega
  unfold Φ
  apply Finset.sum_lt_sum
  · intro u _; exact add_le_add (hle u).1 (hle u).2
  · exact ⟨v, Finset.mem_univ _, hlt⟩

lemma mean_zero {ν : PMF (St w)} {μ : PMF (Finset Page × Prof w)} {y' : Page → ℝ}
    (hfst : ν.map Prod.fst = μ) (hm : ∀ i, ex ν (fun z => ind z.2 i) = y' i)
    (hmean : ∀ v : WClass w, ∑ x, (μ x).toReal * ((x.2 v : ℕ) : ℝ) = classMass w y' v)
    (v : WClass w) : ∑ z, (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) = 0 := by
  have hc : ∀ z, (cnt w v z : ℝ) = ∑ p ∈ cls w v, ind z.2 p := by
    intro z
    unfold cnt ind
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_comm]
  have h1 : ∑ z, (ν z).toReal * (cnt w v z : ℝ) = classMass w y' v := by
    simp only [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    unfold classMass
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hm p]; rfl
  have h2 : ∑ z, (ν z).toReal * (tg w v z : ℝ) = classMass w y' v := by
    have := ex_map ν Prod.fst (fun x => ((x.2 v : ℕ) : ℝ))
    rw [hfst] at this
    rw [← hmean v]
    exact this.symm
  simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_self]

lemma signs {ν : PMF (St w)} {v : WClass w} {z₀ : St w} (hz₀ : ν z₀ ≠ 0)
    (hne : cnt w v z₀ ≠ tg w v z₀) (h0 : ∑ z, (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) = 0) :
    (∃ z, ν z ≠ 0 ∧ tg w v z < cnt w v z) ∧ (∃ z, ν z ≠ 0 ∧ cnt w v z < tg w v z) := by
  constructor
  · by_contra hcon
    push Not at hcon
    have hnp : ∀ z ∈ Finset.univ, (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) ≤ 0 := by
      intro z _
      by_cases hz : ν z = 0
      · simp [hz]
      · apply mul_nonpos_of_nonneg_of_nonpos ENNReal.toReal_nonneg
        have : (cnt w v z : ℝ) ≤ tg w v z := by exact_mod_cast hcon z hz
        linarith
    have h1 := (Finset.sum_eq_zero_iff_of_nonpos hnp).1 h0 z₀ (Finset.mem_univ _)
    have hlt : cnt w v z₀ < tg w v z₀ := lt_of_le_of_ne (hcon z₀ hz₀) hne
    have h2 : (cnt w v z₀ : ℝ) < tg w v z₀ := by exact_mod_cast hlt
    have := mul_neg_of_pos_of_neg (toReal_pos hz₀) (by linarith : (cnt w v z₀ : ℝ) - tg w v z₀ < 0)
    linarith
  · by_contra hcon
    push Not at hcon
    have hnp : ∀ z ∈ Finset.univ, 0 ≤ (ν z).toReal * ((cnt w v z : ℝ) - tg w v z) := by
      intro z _
      by_cases hz : ν z = 0
      · simp [hz]
      · apply mul_nonneg ENNReal.toReal_nonneg
        have : (tg w v z : ℝ) ≤ cnt w v z := by exact_mod_cast hcon z hz
        linarith
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnp).1 h0 z₀ (Finset.mem_univ _)
    have hlt : tg w v z₀ < cnt w v z₀ := lt_of_le_of_ne (hcon z₀ hz₀) (Ne.symm hne)
    have h2 : (tg w v z₀ : ℝ) < cnt w v z₀ := by exact_mod_cast hlt
    have := mul_pos (toReal_pos hz₀) (by linarith : 0 < (cnt w v z₀ : ℝ) - tg w v z₀)
    linarith

lemma PE_pos {ν : PMF (St w)} {v : WClass w} (hE : ∃ z, ν z ≠ 0 ∧ tg w v z < cnt w v z) :
    0 < PE w ν v := by
  obtain ⟨z, hz, h⟩ := hE
  have := Finset.single_le_sum
    (f := fun z => if tg w v z < cnt w v z then (ν z).toReal else 0)
    (fun z _ => by split_ifs <;> simp) (Finset.mem_univ z)
  simp only [h, ↓reduceIte] at this
  exact lt_of_lt_of_le (toReal_pos hz) this

lemma hB_of {μ : PMF (Finset Page × Prof w)} {y' : Page → ℝ} {ν : PMF (St w)}
    (hbound : ∀ x ∈ μ.support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1)
    (hfst : ν.map Prod.fst = μ) :
    ∀ z, ν z ≠ 0 → ∀ u : WClass w, classMass w y' u - 1 < (tg w u z : ℝ) ∧
      (tg w u z : ℝ) < classMass w y' u + 1 := by
  intro z hz u
  have : z.1 ∈ μ.support := by
    rw [← hfst]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨z, (PMF.mem_support_iff _ _).2 hz, rfl⟩
  exact hbound z.1 this u

lemma round_inv (hw : ∀ i, 0 ≤ w i) (K : WClass w → ℝ) {μ : PMF (Finset Page × Prof w)}
    {y' : Page → ℝ} {ν : PMF (St w)} {v : WClass w}
    (hB : ∀ z, ν z ≠ 0 → ∀ u, K u - 1 < (tg w u z : ℝ) ∧ (tg w u z : ℝ) < K u + 1)
    (hM : 0 < MM w ν v) (h : Inv w μ y' ν) : Inv w μ y' (round w ν v) := by
  refine ⟨by rw [round_map_fst, h.1], fun i => by rw [round_marg hM, h.2.1 i], fun z' hz' => ?_⟩
  obtain ⟨z, hz, hF, h1, -⟩ := succ_facts hw K hB hM hz'
  rw [h1]
  exact hF.trans (h.2.2 z hz)

theorem main (hw : ∀ i, 0 ≤ w i) (μ : PMF (Finset Page × Prof w)) (y' : Page → ℝ)
    (hbound : ∀ x ∈ μ.support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1)
    (hmean : ∀ v : WClass w, ∑ x, (μ x).toReal * ((x.2 v : ℕ) : ℝ) = classMass w y' v) :
    ∀ (n : ℕ) (ν : PMF (St w)), Φ w ν = n → Inv w μ y' ν →
      ∃ ν', Inv w μ y' ν' ∧ ∀ z, ν' z ≠ 0 → ∀ u, cnt w u z = tg w u z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ν hn hI
  by_cases hdone : ∀ z, ν z ≠ 0 → ∀ u, cnt w u z = tg w u z
  · exact ⟨ν, hI, hdone⟩
  push Not at hdone
  obtain ⟨z₀, hz₀, v, hne⟩ := hdone
  have hB := hB_of hbound hI.1
  obtain ⟨hE, hH⟩ := signs hz₀ hne (mean_zero hI.1 hI.2.1 hmean v)
  have hM : 0 < MM w ν v := lt_of_lt_of_le (PE_pos hE) (le_max_left _ _)
  exact ih _ (hn ▸ Φ_lt hw _ hB hM hE hH) _ rfl (round_inv hw _ hB hM hI)

end Main

end Transfer

open Transfer in
/-- If the target profiles are `⌊K'_v⌋` or `⌈K'_v⌉` with mean `K'_v` (the class mass of the
marginals `y'`), pages can be moved from caches with an excess in a class to caches with a hole
in it until every cache has its target profile; marginals are preserved, and the fetched pages
are exactly the missing ones. -/
theorem transfer {Page : Type} [Fintype Page] [DecidableEq Page]
    (w : Page → ℝ) (hw : ∀ i, 0 ≤ w i) (y' : Page → ℝ)
    (μ : PMF (Finset Page × Prof w)) (hmarg : ∀ i, margX μ i = y' i)
    (hbound : ∀ x ∈ μ.support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1)
    (hmean : ∀ v : WClass w, ∑ x, (μ x).toReal * ((x.2 v : ℕ) : ℝ) = classMass w y' v) :
    ∃ κ : Finset Page × Prof w → PMF (Finset Page),
      (∀ x ∈ μ.support, ∀ C' ∈ (κ x).support, profile w C' = x.2) ∧
      (∀ i, ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * (if i ∈ C' then 1 else 0) = y' i) ∧
      ∑ x, ∑ C', (μ x).toReal * (κ x C').toReal * ∑ i ∈ C' \ x.1, w i ≤
        ∑ x, (μ x).toReal *
          ∑ v : WClass w, (v : ℝ) * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) := by
  classical
  let ν₀ : PMF (St w) := μ.map (fun x => (x, x.1))
  have hI0 : Inv w μ y' ν₀ := by
    refine ⟨?_, fun i => ?_, fun z hz => ?_⟩
    · show (μ.map _).map Prod.fst = μ
      rw [PMF.map_comp]
      exact PMF.map_id μ
    · show ex (μ.map _) _ = _
      rw [ex_map, ← hmarg i]
      rfl
    · obtain ⟨x, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 ((PMF.mem_support_iff _ _).2 hz)
      apply le_of_eq
      simp [F, G, cnt, tg, profile]
  obtain ⟨ν', ⟨hfst, hm, hF⟩, hfin⟩ := main hw μ y' hbound hmean _ ν₀ rfl hI0
  have hsum := ex_cond ν' μ hfst
  refine ⟨condSnd ν', ?_, ?_, ?_⟩
  · intro x hx C' hC'
    have hne : ν' (x, C') ≠ 0 := condSnd_ne_zero (by rw [hfst]; exact (PMF.mem_support_iff _ _).1 hx)
      ((PMF.mem_support_iff _ _).1 hC')
    funext u
    exact Fin.ext (hfin _ hne u)
  · intro i
    exact (hsum (fun z => ind z.2 i)).trans (hm i)
  · calc _ = ex ν' (fun z => ∑ i ∈ z.2 \ z.1.1, w i) := hsum _
      _ ≤ ex ν' (fun z => G w z.1) := by
        unfold ex
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : ν' z = 0
        · simp [hz]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        refine le_trans ?_ (hF z hz)
        unfold F
        apply le_add_of_nonneg_right
        exact Finset.sum_nonneg fun u _ => mul_nonneg (class_nonneg w hw u) (le_max_left _ _)
      _ = ex μ (G w) := by rw [← hfst, ex_map]; rfl
      _ = _ := rfl

end BBNProof
end

/-! ## Inlined from `BBNProof.BBN` -/
section

/-!
# The online rounding theorem (BBN, Theorem 4.1, fetch-cost version)

Assembly: one step of the rounding draws the target profile `m` from the coupling `rhoLaw`
conditioned on the current profile, fixes the marginals page by page (`add_remove`), and then
moves pages within classes until the cache has profile `m` (`transfer`).
-/

noncomputable section
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace BBNProof

namespace Assembly

/-! ### Conditional distributions of a coupling -/

section Cond

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]

omit [DecidableEq α] in
theorem map_fst_apply (π : PMF (α × β)) (a : α) : π.map Prod.fst a = ∑ b, π (a, b) := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- The conditional distribution of the second coordinate of `π` given the first is `a`. -/
def condSnd (π : PMF (α × β)) (a : α) : PMF β :=
  if h : π.map Prod.fst a = 0 then π.map Prod.snd else
    PMF.ofFintype (fun b => π (a, b) / π.map Prod.fst a) (by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← map_fst_apply]
      exact ENNReal.mul_inv_cancel h (PMF.apply_ne_top _ _))

theorem bind_condSnd (π : PMF (α × β)) :
    (π.map Prod.fst).bind (fun a => (condSnd π a).map (Prod.mk a)) = π := by
  ext ⟨a, b⟩
  have hrow : ∀ a' b', π (a', b') ≤ π.map Prod.fst a' := fun a' b' => by
    rw [map_fst_apply]
    exact Finset.single_le_sum (f := fun b => π (a', b)) (fun _ _ => zero_le)
      (Finset.mem_univ b')
  have hmk : ∀ a' (p : PMF β), p.map (Prod.mk a') (a, b) = if a = a' then p b else 0 := by
    intro a' p
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'
      simp [Ne.symm hb']
    · simp
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single a]
  · rw [hmk, if_pos rfl]
    unfold condSnd
    split_ifs with h
    · simpa [h] using (le_antisymm (h ▸ hrow a b) (zero_le)).symm
    · rw [PMF.ofFintype_apply]
      exact ENNReal.mul_div_cancel h (PMF.apply_ne_top _ _)
  · intro a' _ ha'
    rw [hmk, if_neg (Ne.symm ha'), mul_zero]
  · simp

end Cond

/-! ### Expectations over finite types -/

section Ex

variable {α β : Type} [Fintype α] [Fintype β]

/-- The expectation of `f` under `p`. -/
def ex (p : PMF α) (f : α → ℝ) : ℝ := ∑ a, (p a).toReal * f a

theorem ex_bind (p : PMF α) (K : α → PMF β) (f : β → ℝ) :
    ex (p.bind K) f = ex p (fun a => ex (K a) f) := by
  unfold ex
  have h : ∀ b, ((p.bind K) b).toReal = ∑ a, (p a).toReal * (K a b).toReal := by
    intro b
    rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
    · simp_rw [ENNReal.toReal_mul]
    · intro a _
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  simp_rw [h, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc]

theorem ex_pure (a : α) (f : α → ℝ) : ex (PMF.pure a) f = f a := by
  classical
  unfold ex
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [PMF.pure_apply, hb]
  · simp

theorem ex_map (p : PMF α) (g : α → β) (f : β → ℝ) : ex (p.map g) f = ex p (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, ex_bind]
  simp [ex_pure]

theorem ex_congr (p : PMF α) {f g : α → ℝ} (h : ∀ a ∈ p.support, f a = g a) :
    ex p f = ex p g := by
  unfold ex
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff _ _).2 ha)]

theorem ex_mono (p : PMF α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : ex p f ≤ ex p g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

theorem ex_add (p : PMF α) (f g : α → ℝ) : ex p (fun a => f a + g a) = ex p f + ex p g := by
  unfold ex
  simp_rw [mul_add, Finset.sum_add_distrib]

theorem ex_mul_left (p : PMF α) (c : ℝ) (f : α → ℝ) : ex p (fun a => c * f a) = c * ex p f := by
  unfold ex
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

theorem ex_sum {ι : Type} [Fintype ι] (p : PMF α) (f : ι → α → ℝ) :
    ex p (fun a => ∑ v, f v a) = ∑ v, ex p (f v) := by
  unfold ex
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_toReal (p : PMF α) : ∑ a, (p a).toReal = 1 := by
  have h := p.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a), h]
  simp

theorem ex_const (p : PMF α) (c : ℝ) : ex p (fun _ => c) = c := by
  unfold ex
  rw [← Finset.sum_mul, sum_toReal, one_mul]

theorem sum_sum_eq (p : PMF α) (K : α → PMF β) (f : α → β → ℝ) :
    ∑ a, ∑ b, (p a).toReal * (K a b).toReal * f a b = ex p (fun a => ex (K a) (f a)) := by
  unfold ex
  simp_rw [Finset.mul_sum, mul_assoc]

theorem ext_of_ex [DecidableEq α] {p q : PMF α}
    (h : ∀ a, ex p (fun z => if z = a then 1 else 0) = ex q (fun z => if z = a then 1 else 0)) :
    p = q := by
  have key : ∀ (r : PMF α) a, ex r (fun z => if z = a then 1 else 0) = (r a).toReal := by
    intro r a
    unfold ex
    simp
  ext a
  have := h a
  rw [key, key] at this
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).1 this

end Ex

/-! ### One step of the rounding -/

section Step

variable {Page : Type} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

/-- The weight of the pages of `C'` missing from `C`. -/
def cost (C C' : Finset Page) : ℝ := ∑ i ∈ C' \ C, w i

/-- Draw the cache from `D` and the target profile from `ρ` conditioned on its profile. -/
def mu (D : PMF (Finset Page)) (ρ : PMF (Prof w × Prof w)) : PMF (Finset Page × Prof w) :=
  D.bind fun C => (condSnd ρ (profile w C)).map (Prod.mk C)

/-- Apply `κ` to the cache, keeping the target profile. -/
def mu2 (μ : PMF (Finset Page × Prof w)) (κ : Finset Page × Prof w → PMF (Finset Page)) :
    PMF (Finset Page × Prof w) :=
  μ.bind fun x => (κ x).map fun C'' => (C'', x.2)

/-- The step kernel. -/
def kern (ρ : PMF (Prof w × Prof w)) (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page))
    (C : Finset Page) : PMF (Finset Page) :=
  (condSnd ρ (profile w C)).bind fun m => (κ₁ (C, m)).bind fun C'' => κ₂ (C'', m)

theorem ex_mu (D : PMF (Finset Page)) (ρ : PMF (Prof w × Prof w))
    (h : Finset Page × Prof w → ℝ) :
    ex (mu w D ρ) h = ex D (fun C => ex (condSnd ρ (profile w C)) (fun m => h (C, m))) := by
  unfold mu
  rw [ex_bind]
  simp_rw [ex_map]

theorem ex_mu2 (μ : PMF (Finset Page × Prof w)) (κ : Finset Page × Prof w → PMF (Finset Page))
    (h : Finset Page × Prof w → ℝ) :
    ex (mu2 w μ κ) h = ex μ (fun x => ex (κ x) (fun C'' => h (C'', x.2))) := by
  unfold mu2
  rw [ex_bind]
  simp_rw [ex_map]

theorem ex_kern (ρ : PMF (Prof w × Prof w)) (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page))
    (C : Finset Page) (g : Finset Page → ℝ) :
    ex (kern w ρ κ₁ κ₂ C) g =
      ex (condSnd ρ (profile w C)) (fun m => ex (κ₁ (C, m)) (fun C'' => ex (κ₂ (C'', m)) g)) := by
  unfold kern
  rw [ex_bind]
  simp_rw [ex_bind]

theorem ex_chain (D : PMF (Finset Page)) (ρ : PMF (Prof w × Prof w))
    (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page)) (g : Finset Page → ℝ) :
    ex D (fun C => ex (kern w ρ κ₁ κ₂ C) g) = ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) g) := by
  rw [ex_mu2, ex_mu]
  simp_rw [ex_kern]

theorem mu_map {D : PMF (Finset Page)} {ρ : PMF (Prof w × Prof w)}
    (hD : D.map (profile w) = ρ.map Prod.fst) :
    (mu w D ρ).map (fun x => (profile w x.1, x.2)) = ρ := by
  unfold mu
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  have : (fun C => (condSnd ρ (profile w C)).map
      ((fun x : Finset Page × Prof w => (profile w x.1, x.2)) ∘ Prod.mk C)) =
      (fun a => (condSnd ρ a).map (Prod.mk a)) ∘ profile w := by
    funext C
    rfl
  rw [this, ← PMF.bind_map, hD, bind_condSnd]

theorem ex_mu_prof {D : PMF (Finset Page)} {ρ : PMF (Prof w × Prof w)}
    (hD : D.map (profile w) = ρ.map Prod.fst) (g : Prof w × Prof w → ℝ) :
    ex (mu w D ρ) (fun x => g (profile w x.1, x.2)) = ex ρ g := by
  conv_rhs => rw [← mu_map w hD]
  rw [ex_map]

theorem mu_snd {D : PMF (Finset Page)} {ρ : PMF (Prof w × Prof w)}
    (hD : D.map (profile w) = ρ.map Prod.fst) :
    (mu w D ρ).map Prod.snd = ρ.map Prod.snd := by
  conv_rhs => rw [← mu_map w hD]
  rw [PMF.map_comp]
  rfl

theorem mu2_snd (μ : PMF (Finset Page × Prof w)) (κ : Finset Page × Prof w → PMF (Finset Page)) :
    (mu2 w μ κ).map Prod.snd = μ.map Prod.snd := by
  unfold mu2
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  have : ∀ x : Finset Page × Prof w,
      (κ x).map (Prod.snd ∘ fun C'' => (C'', x.2)) = PMF.pure x.2 := by
    intro x
    exact PMF.map_const (κ x) x.2
  simp_rw [this]
  rfl

theorem marginal_eq_ex (Q : PMF (Finset Page)) (i : Page) :
    marginal Q i = ex Q (fun C => if i ∈ C then 1 else 0) := by
  unfold marginal ex
  refine Finset.sum_congr rfl fun C _ => ?_
  by_cases h : i ∈ C <;> simp [h]

theorem margX_eq_ex (μ : PMF (Finset Page × Prof w)) (i : Page) :
    margX μ i = ex μ (fun x => if i ∈ x.1 then 1 else 0) := rfl

theorem margX_mu {D : PMF (Finset Page)} {y : Page → ℝ} (hD : marginal D = y)
    (ρ : PMF (Prof w × Prof w)) (i : Page) : margX (mu w D ρ) i = y i := by
  rw [margX_eq_ex, ex_mu, ← hD, marginal_eq_ex]
  congr 1
  funext C
  exact ex_const (condSnd ρ (profile w C)) (if i ∈ C then 1 else 0)

theorem wclass_pos (hw : ∀ i, 0 < w i) (v : WClass w) : 0 < (v : ℝ) := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.1 v.2
  rw [← hi]
  exact hw i

/-- The classes partition the pages. -/
theorem sum_cls (f : Page → ℝ) :
    ∑ v : WClass w, (v : ℝ) * ∑ i ∈ cls w v, f i = ∑ i, w i * f i := by
  have h1 : ∀ v : WClass w, (v : ℝ) * ∑ i ∈ cls w v, f i = ∑ i ∈ cls w v, w i * f i := by
    intro v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  simp_rw [h1]
  exact (Finset.sum_coe_sort (Finset.univ.image w) (fun v => ∑ i ∈ cls w v, w i * f i)).trans
    (Finset.sum_fiberwise_of_maps_to
      (fun i _ => Finset.mem_image_of_mem w (Finset.mem_univ i)) _)

theorem cost_le (C C'' C' : Finset Page) (hw : ∀ i, 0 ≤ w i) :
    cost w C C' ≤ cost w C'' C' + cost w C C'' := by
  unfold cost
  rw [← Finset.sum_union]
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => hw i
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_union] at hi ⊢
    by_cases h : i ∈ C'' <;> tauto
  · rw [Finset.disjoint_left]
    intro i h1 h2
    exact (Finset.mem_sdiff.1 h1).2 (Finset.mem_sdiff.1 h2).1

theorem max_add_max (a b : ℝ) : max 0 (a - b) + max 0 (b - a) = |b - a| := by
  rcases le_total a b with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]
    ring

/-- The hypotheses of `transfer` for the distribution after `add_remove`. -/
theorem mu2_hyps {k : ℕ} {y y' : Page → ℝ} (hy' : y' ∈ fracCaches k) {D : PMF (Finset Page)}
    (hD : InClass w y D) (κ₁ : Finset Page × Prof w → PMF (Finset Page))
    (hκ₁ : ∀ i, ∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal *
      (if i ∈ C' then 1 else 0) = y' i) :
    (∀ i, margX (mu2 w (mu w D (rhoLaw w y y')) κ₁) i = y' i) ∧
    (∀ x ∈ (mu2 w (mu w D (rhoLaw w y y')) κ₁).support, ∀ v : WClass w,
      classMass w y' v - 1 < ((x.2 v : ℕ) : ℝ) ∧ ((x.2 v : ℕ) : ℝ) < classMass w y' v + 1) ∧
    (∀ v : WClass w, ∑ x, ((mu2 w (mu w D (rhoLaw w y y')) κ₁) x).toReal * ((x.2 v : ℕ) : ℝ) =
      classMass w y' v) := by
  have hDρ : D.map (profile w) = (rhoLaw w y y').map Prod.fst :=
    hD.1.trans (rhoLaw_fst w y y').symm
  have hsnd : (mu2 w (mu w D (rhoLaw w y y')) κ₁).map Prod.snd = profLaw w y' := by
    rw [mu2_snd, mu_snd w hDρ, rhoLaw_snd]
  refine ⟨fun i => ?_, fun x hx v => ?_, fun v => ?_⟩
  · rw [margX_eq_ex, ex_mu2, ← hκ₁ i, sum_sum_eq]
  · have : x.2 ∈ (profLaw w y').support := by
      rw [← hsnd]
      exact (PMF.mem_support_map_iff _ _ _).2 ⟨x, hx, rfl⟩
    exact profLaw_bounds w hy' this v
  · have h := ex_map (mu2 w (mu w D (rhoLaw w y y')) κ₁) Prod.snd (fun c => ((c v : ℕ) : ℝ))
    rw [hsnd] at h
    exact h.symm.trans (profLaw_mean w hy' v)

end Step

/-! ### The step and its guarantees -/

section Main

variable {Page : Type} [Fintype Page] [DecidableEq Page] (w : Page → ℝ)

theorem step_spec (hw : ∀ i, 0 < w i) (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) {k : ℕ}
    {y y' : Page → ℝ} (hy : y ∈ fracCaches k) (hy' : y' ∈ fracCaches k) {D : PMF (Finset Page)}
    (hD : InClass w y D) (κ₁ κ₂ : Finset Page × Prof w → PMF (Finset Page))
    (hκ₁ : (∀ i, ∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal *
          (if i ∈ C' then 1 else 0) = y' i) ∧
      (∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal * ∑ i ∈ C' \ x.1, w i ≤
        ∑ i, w i * max 0 (y' i - margX (mu w D (rhoLaw w y y')) i)) ∧
      (∀ v : WClass w,
        ∑ x, ∑ C', (mu w D (rhoLaw w y y') x).toReal * (κ₁ x C').toReal *
            max 0 (((x.2 v : ℕ) : ℝ) - ((profile w C' v : ℕ) : ℝ)) ≤
          ∑ x, (mu w D (rhoLaw w y y') x).toReal *
              max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)) +
            ∑ i ∈ cls w v, max 0 (margX (mu w D (rhoLaw w y y')) i - y' i)))
    (hκ₂ : (∀ x ∈ (mu2 w (mu w D (rhoLaw w y y')) κ₁).support, ∀ C' ∈ (κ₂ x).support,
          profile w C' = x.2) ∧
      (∀ i, ∑ x, ∑ C', (mu2 w (mu w D (rhoLaw w y y')) κ₁ x).toReal * (κ₂ x C').toReal *
          (if i ∈ C' then 1 else 0) = y' i) ∧
      ∑ x, ∑ C', (mu2 w (mu w D (rhoLaw w y y')) κ₁ x).toReal * (κ₂ x C').toReal *
          ∑ i ∈ C' \ x.1, w i ≤
        ∑ x, (mu2 w (mu w D (rhoLaw w y y')) κ₁ x).toReal *
          ∑ v : WClass w, (v : ℝ) * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) :
    InClass w y' (D.bind (kern w (rhoLaw w y y') κ₁ κ₂)) ∧
      ∑ C, ∑ C', (D C).toReal * (kern w (rhoLaw w y y') κ₁ κ₂ C C').toReal * ∑ i ∈ C' \ C, w i ≤
        4 * ∑ i, w i * |y' i - y i| := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hρ1 := rhoLaw_fst w y y'
  have hρ2 := rhoLaw_snd w y y'
  have hρ3 := rhoLaw_move w hw hw2 hy hy'
  generalize rhoLaw w y y' = ρ at hρ1 hρ2 hρ3 hκ₁ hκ₂ ⊢
  have hDρ : D.map (profile w) = ρ.map Prod.fst := hD.1.trans hρ1.symm
  have hsnd : (mu2 w (mu w D ρ) κ₁).map Prod.snd = profLaw w y' := by
    rw [mu2_snd, mu_snd w hDρ, hρ2]
  have hmy : ∀ i, margX (mu w D ρ) i = y i := margX_mu w hD.2 ρ
  obtain ⟨hk1, hk2, hk3⟩ := hκ₁
  obtain ⟨hp1, hp2, hp3⟩ := hκ₂
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · classical
    apply ext_of_ex
    intro c
    simp only [ex_map, ex_bind, ex_chain]
    have : ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (fun C' => if profile w C' = c then 1 else 0))
        = ex (mu2 w (mu w D ρ) κ₁) (fun x => if x.2 = c then 1 else 0) := by
      apply ex_congr
      intro x hx
      rw [ex_congr (κ₂ x) (g := fun _ => if x.2 = c then 1 else 0)
        (fun C' hC' => by rw [hp1 x hx C' hC']), ex_const]
    rw [this, ← hsnd, ex_map]
  · funext i
    rw [marginal_eq_ex, ex_bind, ex_chain, ← hp2 i, sum_sum_eq]
  · rw [sum_sum_eq]
    show ex D (fun C => ex (kern w ρ κ₁ κ₂ C) (cost w C)) ≤ _
    have e1 : ex D (fun C => ex (kern w ρ κ₁ κ₂ C) (cost w C)) =
        ex (mu w D ρ) (fun x => ex (κ₁ x) (fun C'' => ex (κ₂ (C'', x.2)) (cost w x.1))) := by
      rw [ex_mu]
      simp_rw [ex_kern]
    have e2 : ex (mu w D ρ) (fun x => ex (κ₁ x) (fun C'' => ex (κ₂ (C'', x.2)) (cost w x.1))) ≤
        ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (cost w x.1)) +
          ex (mu w D ρ) (fun x => ex (κ₁ x) (cost w x.1)) := by
      rw [ex_mu2, ← ex_add]
      refine ex_mono _ fun x => ?_
      rw [← ex_add]
      refine ex_mono _ fun C'' => ?_
      calc ex (κ₂ (C'', x.2)) (cost w x.1)
          ≤ ex (κ₂ (C'', x.2)) (fun C' => cost w C'' C' + cost w x.1 C'') :=
            ex_mono _ fun C' => cost_le w _ _ _ hw0
        _ = ex (κ₂ (C'', x.2)) (cost w C'') + cost w x.1 C'' := by
            rw [ex_add, ex_const]
    have hA : ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (cost w x.1)) ≤
        ∑ v : WClass w, (v : ℝ) *
          (ex (mu w D ρ) (fun x => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) +
            ∑ i ∈ cls w v, max 0 (margX (mu w D ρ) i - y' i)) := by
      calc ex (mu2 w (mu w D ρ) κ₁) (fun x => ex (κ₂ x) (cost w x.1))
          ≤ ex (mu2 w (mu w D ρ) κ₁) (fun x => ∑ v : WClass w,
              (v : ℝ) * max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) := by
            have := hp3
            rw [sum_sum_eq] at this
            exact this
        _ = ∑ v : WClass w, (v : ℝ) * ex (mu w D ρ) (fun x => ex (κ₁ x)
              (fun C'' => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w C'' v : ℕ) : ℝ)))) := by
            rw [ex_mu2]
            simp_rw [ex_sum, ex_mul_left]
        _ ≤ _ := by
            refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (wclass_pos w hw v).le
            have := hk3 v
            rw [sum_sum_eq] at this
            exact this
    have hB : ex (mu w D ρ) (fun x => ex (κ₁ x) (cost w x.1)) ≤
        ∑ i, w i * max 0 (y' i - margX (mu w D ρ) i) := by
      have := hk2
      rw [sum_sum_eq] at this
      exact this
    have hmove : ∑ v : WClass w, (v : ℝ) * ex (mu w D ρ)
          (fun x => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ))) ≤
        3 * ∑ i, w i * |y' i - y i| := by
      calc ∑ v : WClass w, (v : ℝ) * ex (mu w D ρ)
            (fun x => max 0 (((x.2 v : ℕ) : ℝ) - ((profile w x.1 v : ℕ) : ℝ)))
          = ∑ v : WClass w, (v : ℝ) * ex ρ
              (fun z => max 0 (((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ))) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [ex_mu_prof w hDρ (fun z => max 0 (((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ)))]
        _ ≤ ∑ v : WClass w, (v : ℝ) * ex ρ
              (fun z => |((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ)|) := by
            refine Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ (wclass_pos w hw v).le
            exact ex_mono _ fun z => max_le (abs_nonneg _) (le_abs_self _)
        _ = ex ρ (fun z => ∑ v : WClass w, (v : ℝ) * |((z.2 v : ℕ) : ℝ) - ((z.1 v : ℕ) : ℝ)|) := by
            rw [ex_sum]
            simp_rw [ex_mul_left]
        _ ≤ _ := hρ3
    have hcls : ∑ v : WClass w, (v : ℝ) * ∑ i ∈ cls w v, max 0 (margX (mu w D ρ) i - y' i) +
        ∑ i, w i * max 0 (y' i - margX (mu w D ρ) i) = ∑ i, w i * |y' i - y i| := by
      simp_rw [hmy]
      rw [sum_cls, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_add, max_add_max]
    simp_rw [mul_add, Finset.sum_add_distrib] at hA
    have hpos : 0 ≤ ∑ i, w i * |y' i - y i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (abs_nonneg _)
    linarith

/-- The kernel of `add_remove` for `μ = mu w D (rhoLaw w y y')`. -/
def kappa1 (hw0 : ∀ i, 0 ≤ w i) (D : PMF (Finset Page)) (y y' : Page → ℝ)
    (hy' : ∀ i, 0 ≤ y' i ∧ y' i ≤ 1) : Finset Page × Prof w → PMF (Finset Page) :=
  Classical.choose (add_remove w hw0 y' hy' (mu w D (rhoLaw w y y')))

/-- The kernel of `transfer` for `μ₂ = mu2 w μ (kappa1 …)`. -/
def kappa2 (hw0 : ∀ i, 0 ≤ w i) {k : ℕ} (D : PMF (Finset Page)) (y y' : Page → ℝ)
    (H : y ∈ fracCaches k ∧ y' ∈ fracCaches k ∧ InClass w y D) :
    Finset Page × Prof w → PMF (Finset Page) :=
  Classical.choose (transfer w hw0 y' (mu2 w (mu w D (rhoLaw w y y')) (kappa1 w hw0 D y y' H.2.1.1))
    (mu2_hyps w H.2.1 H.2.2 _
      (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).1
    (mu2_hyps w H.2.1 H.2.2 _
      (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.1
    (mu2_hyps w H.2.1 H.2.2 _
      (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.2)

open Classical in
/-- The rounding map (the identity kernel when the hypotheses fail). -/
def Tmap (hw0 : ∀ i, 0 ≤ w i) (k : ℕ) (D : PMF (Finset Page)) (y y' : Page → ℝ) :
    Finset Page → PMF (Finset Page) :=
  if H : y ∈ fracCaches k ∧ y' ∈ fracCaches k ∧ InClass w y D then
    kern w (rhoLaw w y y') (kappa1 w hw0 D y y' H.2.1.1) (kappa2 w hw0 D y y' H)
  else fun C => PMF.pure C

end Main

end Assembly

end BBNProof

namespace BBNProof

variable {Page : Type} [Fintype Page] [DecidableEq Page]

open Assembly in
/-- **Online rounding for weighted paging** (Bansal–Buchbinder–Naor, Theorem 4.1, fetch-cost
version with constant `4`). -/
theorem bbn_rounding (w : Page → ℝ) (hw : ∀ i, 0 < w i)
    (hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j) (k : ℕ) :
    ∃ T : PMF (Finset Page) → (Page → ℝ) → (Page → ℝ) → Finset Page → PMF (Finset Page),
      ∀ D y y', y ∈ fracCaches k → y' ∈ fracCaches k → InClass w y D →
        InClass w y' (D.bind (T D y y')) ∧
        ∑ C, ∑ C', (D C).toReal * (T D y y' C C').toReal * ∑ i ∈ C' \ C, w i ≤
          4 * ∑ i, w i * |y' i - y i| := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  refine ⟨Tmap w hw0 k, fun D y y' hy hy' hD => ?_⟩
  have H : y ∈ fracCaches k ∧ y' ∈ fracCaches k ∧ InClass w y D := ⟨hy, hy', hD⟩
  rw [Tmap, dif_pos H]
  exact step_spec w hw hw2 hy hy' hD _ _
    (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y'))))
    (Classical.choose_spec (transfer w hw0 y'
      (mu2 w (mu w D (rhoLaw w y y')) (kappa1 w hw0 D y y' H.2.1.1))
      (mu2_hyps w H.2.1 H.2.2 _
        (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).1
      (mu2_hyps w H.2.1 H.2.2 _
        (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.1
      (mu2_hyps w H.2.1 H.2.2 _
        (Classical.choose_spec (add_remove w hw0 y' H.2.1.1 (mu w D (rhoLaw w y y')))).1).2.2))

theorem inClass_pure (w : Page → ℝ) (C₀ : Finset Page) :
    InClass w (indicator C₀) (PMF.pure C₀) := by
  refine ⟨by rw [PMF.pure_map, profLaw_indicator], ?_⟩
  funext i
  unfold marginal indicator
  rw [Finset.sum_eq_single C₀]
  · simp
  · intro C _ hC
    simp [PMF.pure_apply, hC]
  · simp

theorem card_of_inClass (w : Page → ℝ) {k : ℕ} {y : Page → ℝ} (hy : y ∈ fracCaches k)
    {D : PMF (Finset Page)} (hD : InClass w y D) : ∀ C ∈ D.support, C.card = k := by
  intro C hC
  have : profile w C ∈ (profLaw w y).support := by
    rw [← hD.1]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨C, hC, rfl⟩
  exact card_of_profLaw w hy this C rfl

end BBNProof
end

/-! ## Inlined from `BBNProof.Corollary33` -/
section

/-!
# Corollary 33: online rounding with exact marginals, per seed

The kernels of `bbn_rounding` are chained along the history of fractional caches and realized
per seed (`run`): the seed is a sequence of independent uniform variables, and step `ν` draws the
next cache from the kernel by inverse-CDF sampling with the `ν`-th variable.
-/

noncomputable section

open MeasureTheory

namespace BBNProof

namespace Cor33

variable {n : ℕ}

lemma indicator_eq (O₀ : Finset (Fin n)) :
    PagingDelay.PMD.indicator O₀ = BBNProof.indicator O₀ := by
  funext i
  simp only [PagingDelay.PMD.indicator, BBNProof.indicator]

lemma fracCache_iff (k : ℕ) (y : Fin n → ℝ) :
    PagingDelay.PMD.FractionalCache k y ↔ y ∈ fracCaches k := Iff.rfl

/-- The set of seeds whose state contains page `i` is a finite union of the level sets. -/
lemma setOf_mem_eq {S Y : Type} [Fintype S] [DecidableEq S] {s₀ : S}
    {step : PMF S → List Y → Y → S → PMF S} (ys : List Y) (P : S → Prop) [DecidablePred P] :
    {ω : ℕ → ℝ | P (run s₀ step ω ys)} =
      ⋃ s ∈ Finset.univ.filter P, {ω | run s₀ step ω ys = s} := by
  ext ω
  simp

lemma measurableSet_pred {S Y : Type} [Fintype S] [DecidableEq S] (s₀ : S)
    (step : PMF S → List Y → Y → S → PMF S) (ys : List Y) (P : S → Prop) [DecidablePred P] :
    MeasurableSet {ω : ℕ → ℝ | P (run s₀ step ω ys)} := by
  rw [setOf_mem_eq ys P]
  exact Finset.measurableSet_biUnion _ fun s _ => measurableSet_run s₀ step ys s

lemma seedLaw_pred {S Y : Type} [Fintype S] [DecidableEq S] (s₀ : S)
    (step : PMF S → List Y → Y → S → PMF S) (ys : List Y) (P : S → Prop) [DecidablePred P] :
    seedLaw {ω : ℕ → ℝ | P (run s₀ step ω ys)} =
      ∑ s ∈ Finset.univ.filter P, lawOf s₀ step ys s := by
  rw [setOf_mem_eq ys P, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun s _ => seedLaw_run s₀ step ys s
  · intro a _ b _ hab
    exact Set.disjoint_left.2 fun ω ha hb => hab (ha.symm.trans hb)
  · exact fun s _ => measurableSet_run s₀ step ys s

/-- `∑ (Q C).toReal [i ∈ C]` in `ENNReal`. -/
lemma sum_filter_eq_ofReal_marginal {Page : Type} [Fintype Page] [DecidableEq Page]
    (Q : PMF (Finset Page)) (i : Page) :
    ∑ s ∈ Finset.univ.filter (fun s : Finset Page => i ∈ s), Q s =
      ENNReal.ofReal (marginal Q i) := by
  rw [marginal, ← Finset.sum_filter, ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
  exact Finset.sum_congr rfl fun s _ => (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm

end Cor33

open Cor33 in
/-- **Corollary 33** (online rounding with exact marginals). -/
theorem corollary_33 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (w : Fin n → ℝ) (hw : PagingDelay.PMD.DyadicWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k) :
    ∃ R : PagingDelay.PMD.OnlineRounding n,
      (∀ ω, R.choose ω [PagingDelay.PMD.indicator O₀] = O₀) ∧
      (∀ ys, PagingDelay.PMD.CacheHistory k O₀ ys →
        (∀ ω, (R.choose ω ys).card = k) ∧
        (∀ i, PagingDelay.PMD.roundingMarginal R ys i =
          ENNReal.ofReal (ys.getLastD (PagingDelay.PMD.indicator O₀) i)) ∧
        (∀ y, PagingDelay.PMD.FractionalCache k y → PagingDelay.PMD.roundingFetch w R ys y ≤
          ENNReal.ofReal (5 * ∑ i, w i * |y i - ys.getLastD (PagingDelay.PMD.indicator O₀) i|))) := by
  classical
  -- dyadic weights are positive and distinct ones differ by a factor `≥ 2`
  have hpos : ∀ i, 0 < w i := fun i => by
    obtain ⟨m, hm⟩ := hw i
    rw [hm]; positivity
  have hw2 : ∀ i j, w i < w j → 2 * w i ≤ w j := fun i j hij => by
    obtain ⟨a, ha⟩ := hw i
    obtain ⟨b, hb⟩ := hw j
    rw [ha, hb] at hij ⊢
    have hab : a < b := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 hij
    calc 2 * (2 : ℝ) ^ a = 2 ^ (a + 1) := by ring
      _ ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hab
  obtain ⟨T, hT⟩ := bbn_rounding w hpos hw2 k
  set y₀ : Fin n → ℝ := PagingDelay.PMD.indicator O₀ with hy₀
  let step : PMF (Finset (Fin n)) → List (Fin n → ℝ) → (Fin n → ℝ) → Finset (Fin n) →
      PMF (Finset (Fin n)) := fun D ys y => T D (ys.getLastD y₀) y
  let R : PagingDelay.PMD.OnlineRounding n :=
    { Seed := ℕ → ℝ
      measurableSpace := inferInstance
      law := seedLaw
      probability := inferInstance
      choose := fun ω ys => run O₀ step ω ys
      measurable := fun ys i => measurableSet_pred O₀ step ys (fun s => i ∈ s) }
  -- the law after a cache history lies in `𝒟` of its last fractional cache
  have hinv : ∀ ys, PagingDelay.PMD.CacheHistory k O₀ ys →
      InClass w (ys.getLastD y₀) (lawOf O₀ step ys) := by
    intro ys
    induction ys using List.reverseRecOn with
    | nil => intro h; simp [PagingDelay.PMD.CacheHistory] at h
    | append_singleton zs y ih =>
      intro h
      by_cases hzs : zs = []
      · subst hzs
        obtain ⟨hhead, -⟩ := h
        simp only [List.nil_append, List.head?_cons, Option.some.injEq] at hhead
        rw [List.nil_append, lawOf_singleton, List.getLastD_cons, List.getLastD_nil, hhead, indicator_eq]
        exact inClass_pure w O₀
      · have hzs' : PagingDelay.PMD.CacheHistory k O₀ zs := by
          obtain ⟨hhead, hall⟩ := h
          refine ⟨?_, fun z hz => hall z (List.mem_append_left _ hz)⟩
          obtain ⟨a, as, rfl⟩ := List.exists_cons_of_ne_nil hzs
          simpa using hhead
        have hlast : zs.getLastD y₀ ∈ fracCaches k := by
          rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hzs]
          exact h.2 _ (List.mem_append_left _ (List.getLast_mem hzs))
        have hy : y ∈ fracCaches k := h.2 y (by simp)
        rw [lawOf_snoc O₀ step zs hzs y, List.getLastD_concat]
        exact (hT _ _ _ hlast hy (ih hzs')).1
  refine ⟨R, fun ω => run_singleton O₀ step ω y₀, fun ys hys => ?_⟩
  have hne : ys ≠ [] := by
    rintro rfl; simp [PagingDelay.PMD.CacheHistory] at hys
  have hlast : ys.getLastD y₀ ∈ fracCaches k := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    exact hys.2 _ (List.getLast_mem hne)
  have hD := hinv ys hys
  refine ⟨fun ω => card_of_inClass w hlast hD _ (run_mem_support O₀ step ω ys), fun i => ?_,
    fun y hy => ?_⟩
  · change seedLaw {ω | i ∈ run O₀ step ω ys} = _
    rw [seedLaw_pred O₀ step ys (fun s => i ∈ s), sum_filter_eq_ofReal_marginal, hD.2]
  · change ∫⁻ ω, ∑ i ∈ run O₀ step ω (ys ++ [y]) \ run O₀ step ω ys, ENNReal.ofReal (w i)
        ∂seedLaw ≤ _
    rw [lintegral_run_pair O₀ step ys hne y
      (fun s s' => ∑ i ∈ s' \ s, ENNReal.ofReal (w i))]
    obtain ⟨-, hcost⟩ := hT _ _ y hlast ((fracCache_iff k y).1 hy) hD
    set D := lawOf O₀ step ys
    set K := step D ys y
    have hK : K = T D (ys.getLastD y₀) y := rfl
    -- convert the `ENNReal` sum to the real one
    have hconv : ∑ s, ∑ s', D s * K s s' * ∑ i ∈ s' \ s, ENNReal.ofReal (w i) =
        ENNReal.ofReal (∑ s, ∑ s', (D s).toReal * (K s s').toReal * ∑ i ∈ s' \ s, w i) := by
      have hnn : ∀ s s' : Finset (Fin n),
          0 ≤ (D s).toReal * (K s s').toReal * ∑ i ∈ s' \ s, w i := fun s s' =>
        mul_nonneg (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
          (Finset.sum_nonneg fun i _ => (hpos i).le)
      rw [ENNReal.ofReal_sum_of_nonneg fun s _ => Finset.sum_nonneg fun s' _ => hnn s s']
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ENNReal.ofReal_sum_of_nonneg fun s' _ => hnn s s']
      refine Finset.sum_congr rfl fun s' _ => ?_
      rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
        ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
        ENNReal.ofReal_sum_of_nonneg fun i _ => (hpos i).le]
    rw [hconv]
    refine ENNReal.ofReal_le_ofReal ?_
    have hS : 0 ≤ ∑ i, w i * |y i - ys.getLastD y₀ i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hpos i).le (abs_nonneg _)
    rw [hK]
    linarith

end BBNProof
end

open PagingDelay.PMD in
theorem solution (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n)
    (w : Fin n → ℝ) (hw : DyadicWeights w)
    (O₀ : Finset (Fin n)) (hO₀ : O₀.card = k) :
    ∃ R : OnlineRounding n,
      (∀ ω, R.choose ω [indicator O₀] = O₀) ∧
      (∀ ys, CacheHistory k O₀ ys →
        (∀ ω, (R.choose ω ys).card = k) ∧
        (∀ i, roundingMarginal R ys i = ENNReal.ofReal (ys.getLastD (indicator O₀) i)) ∧
        (∀ y, FractionalCache k y → roundingFetch w R ys y ≤
          ENNReal.ofReal (5 * ∑ i, w i * |y i - ys.getLastD (indicator O₀) i|))) :=
  BBNProof.corollary_33 n k hk hkn w hw O₀ hO₀
