-- Prove2me | solution 1 for TsengBCD.Hemivariate.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T00:08:14.011995+00:00
-- url     : https://prove2.me/submissions/99416979-4b49-46c6-894d-aa5d264ddb92

import Mathlib
import Definitions.Def_TsengBCD_Hemivariate_Setting
open Filter Topology
open TsengBCD.Stationary TsengBCD.Hemivariate

namespace TsengHemivariateProof

noncomputable def partialObjective {N : ℕ} {n : Fin N → ℕ}
    (f0 : X n → EReal) (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal)
    (k : Fin N) (x : X n) : EReal := f0 x + fk k (x k)

end TsengHemivariateProof

open Filter Topology
open TsengBCD.Stationary TsengBCD.Hemivariate

namespace TsengHemivariateProof

lemma sum_ne_bot {ι : Type*} (s : Finset ι) (a : ι → EReal)
    (ha : ∀ i ∈ s, a i ≠ ⊥) : ∑ i ∈ s, a i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact EReal.add_ne_bot_iff.mpr ⟨ha i (by simp), ih (fun j hj => ha j (by simp [hj]))⟩

lemma sum_ne_top_iff {ι : Type*} (s : Finset ι) (a : ι → EReal)
    (ha : ∀ i ∈ s, a i ≠ ⊥) : (∑ i ∈ s, a i) ≠ ⊤ ↔ ∀ i ∈ s, a i ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, EReal.add_ne_top_iff_ne_top₂ (ha i (by simp))
      (sum_ne_bot s a (fun j hj => ha j (by simp [hj]))), ih (fun j hj => ha j (by simp [hj]))]
    simp

lemma sum_lsc {α ι : Type*} [TopologicalSpace α] (s : Finset ι) (a : ι → α → EReal)
    (ha : ∀ i ∈ s, LowerSemicontinuous (a i))
    (hb : ∀ i ∈ s, ∀ x, a i x ≠ ⊥) : LowerSemicontinuous (fun x => ∑ i ∈ s, a i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuous_const : Continuous (fun _ : α => (0 : EReal))).lowerSemicontinuous
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    apply (ha i (by simp)).add' (ih (fun j hj => ha j (by simp [hj]))
      (fun j hj => hb j (by simp [hj])))
    intro x
    exact EReal.continuousAt_add (Or.inr (sum_ne_bot s (fun j => a j x)
      (fun j hj => hb j (by simp [hj]) x))) (Or.inl (hb i (by simp) x))

variable {N : ℕ} {n : Fin N → ℕ}
variable {f0 : X n → EReal} {fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal}

lemma objective_ne_bot (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (x : X n) : fSum f0 fk x ≠ ⊥ :=
  EReal.add_ne_bot_iff.mpr ⟨h0bot x, sum_ne_bot Finset.univ _ (fun k _ => hkbot k (x k))⟩

lemma objective_finite (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    {x : X n} (hx : fSum f0 fk x ≠ ⊤) : f0 x ≠ ⊤ ∧ ∀ k, fk k (x k) ≠ ⊤ := by
  have h := (EReal.add_ne_top_iff_ne_top₂ (h0bot x)
    (sum_ne_bot Finset.univ _ (fun k _ => hkbot k (x k)))).mp hx
  exact ⟨h.1, fun k => (sum_ne_top_iff Finset.univ _ (fun j _ => hkbot j (x j))).mp h.2 k (by simp)⟩

lemma objective_lsc (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB3 : AssumptionB3 f0 fk) : LowerSemicontinuous (fSum f0 fk) := by
  apply hB3.1.add' (sum_lsc Finset.univ (fun k (x : X n) => fk k (x k))
    (fun k _ => (hB3.2 k).comp (continuous_apply k)) (fun k _ x => hkbot k (x k)))
  intro x
  exact EReal.continuousAt_add (Or.inr (sum_ne_bot Finset.univ _ (fun k _ => hkbot k (x k))))
    (Or.inl (h0bot x))

lemma partial_lsc (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB3 : AssumptionB3 f0 fk) (k : Fin N) : LowerSemicontinuous (partialObjective f0 fk k) :=
  hB3.1.add' ((hB3.2 k).comp (continuous_apply k))
    (fun x => EReal.continuousAt_add (Or.inr (hkbot k (x k))) (Or.inl (h0bot x)))

lemma objective_split (k : Fin N) (x : X n) :
    fSum f0 fk x = partialObjective f0 fk k x + ∑ j ∈ Finset.univ.erase k, fk j (x j) := by
  classical
  unfold fSum partialObjective
  rw [← Finset.add_sum_erase Finset.univ (fun j => fk j (x j)) (Finset.mem_univ k)]
  exact (add_assoc _ _ _).symm

lemma block_le_iff_partial_le (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    {x y : X n} {k : Fin N} (hx : fSum f0 fk x ≠ ⊤)
    (hxy : ∀ j, j ≠ k → y j = x j) :
    fSum f0 fk x ≤ fSum f0 fk y ↔ partialObjective f0 fk k x ≤ partialObjective f0 fk k y := by
  classical
  have he : (∑ j ∈ Finset.univ.erase k, fk j (y j)) = ∑ j ∈ Finset.univ.erase k, fk j (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hxy j (Finset.mem_erase.mp hj).1]
  have ht := (sum_ne_top_iff (Finset.univ.erase k) (fun j => fk j (x j))
    (fun j _ => hkbot j (x j))).mpr (fun j _ => (objective_finite h0bot hkbot hx).2 j)
  have hb := sum_ne_bot (Finset.univ.erase k) (fun j => fk j (x j)) (fun j _ => hkbot j (x j))
  rw [objective_split k x, objective_split k y, he, ← EReal.coe_toReal ht hb]
  exact (EReal.addLECancellable_coe _).add_le_add_iff_right

lemma partial_difference (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    {x y : X n} {k : Fin N} (hx : fSum f0 fk x ≠ ⊤) (hy : fSum f0 fk y ≠ ⊤)
    (hxy : ∀ j, j ≠ k → y j = x j) :
    (fSum f0 fk x).toReal - (fSum f0 fk y).toReal =
      (partialObjective f0 fk k x).toReal - (partialObjective f0 fk k y).toReal := by
  classical
  have he : (∑ j ∈ Finset.univ.erase k, fk j (y j)) = ∑ j ∈ Finset.univ.erase k, fk j (x j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hxy j (Finset.mem_erase.mp hj).1]
  have ht := (sum_ne_top_iff (Finset.univ.erase k) (fun j => fk j (x j))
    (fun j _ => hkbot j (x j))).mpr (fun j _ => (objective_finite h0bot hkbot hx).2 j)
  have hb := sum_ne_bot (Finset.univ.erase k) (fun j => fk j (x j)) (fun j _ => hkbot j (x j))
  have hp (z : X n) (hz : fSum f0 fk z ≠ ⊤) : partialObjective f0 fk k z ≠ ⊤ :=
    EReal.add_ne_top (objective_finite h0bot hkbot hz).1 ((objective_finite h0bot hkbot hz).2 k)
  have hpb (z : X n) : partialObjective f0 fk k z ≠ ⊥ :=
    EReal.add_ne_bot_iff.mpr ⟨h0bot z, hkbot k (z k)⟩
  rw [objective_split k x, objective_split k y, he,
    EReal.toReal_add (hp x hx) (hpb x) ht hb, EReal.toReal_add (hp y hy) (hpb y) ht hb]
  ring

lemma quasi_hemi_min_unique {V : Type*} [AddCommGroup V] [Module ℝ V]
    {h : V → EReal} (hq : IsQuasiconvex h) (hh : IsHemivariate h)
    {x y : V} (hx : h x ≠ ⊤) (hxmin : ∀ z, h x ≤ h z) (hymin : ∀ z, h y ≤ h z) : x = y := by
  by_contra hne
  have he : h y = h x := le_antisymm (hymin x) (hxmin y)
  have hc : ∀ p ∈ segment ℝ x y, h p = h x := by
    intro p hp
    rw [segment_eq_image'] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    apply le_antisymm _ (hxmin _)
    simpa [he] using hq x (y - x) t ht
  obtain ⟨p, hp, q, hq', hneq⟩ := hh x y hne (fun z hz => by simpa [hc z hz] using hx)
  exact hneq ((hc p hp).trans (hc q hq').symm)

end TsengHemivariateProof

open Filter Topology
open TsengBCD.Stationary TsengBCD.Hemivariate

namespace TsengHemivariateProof

variable {N : ℕ} {n : Fin N → ℕ}
variable {f0 : X n → EReal} {fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal}

lemma compact_level (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB3 : AssumptionB3 f0 fk) {x0 : X n} (_hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0)) :
    IsCompact (levelSet (fSum f0 fk) x0) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨(objective_lsc h0bot hkbot hB3).isClosed_preimage _, hbdd⟩

lemma run_descent {f : X n → EReal} {s : ℕ → Fin N} {x : ℕ → X n}
    (hrun : IsBCDRun f s x) (r : ℕ) : f (x (r+1)) ≤ f (x r) := by
  simpa using (hrun.2 r).2 (x r (s r))

lemma run_level {f : X n → EReal} {s : ℕ → Fin N} {x : ℕ → X n} {x0 : X n}
    (hinit : x 0 = x0) (hrun : IsBCDRun f s x) : ∀ r, x r ∈ levelSet f x0 := by
  intro r
  change f (x r) ≤ f x0
  rw [← hinit]
  exact (antitone_nat_of_succ_le (f := fun r => f (x r)) (run_descent hrun)) (Nat.zero_le r)

lemma block_min_exists (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB3 : AssumptionB3 f0 fk) {x0 : X n} (hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0))
    {a : X n} (ha : a ∈ levelSet (fSum f0 fk) x0) (k : Fin N) :
    ∃ b ∈ levelSet (fSum f0 fk) x0, (∀ j, j ≠ k → b j = a j) ∧
      ∀ y, fSum f0 fk b ≤ fSum f0 fk (Function.update a k y) := by
  classical
  let S : Set (X n) := levelSet (fSum f0 fk) x0 ∩ {b | ∀ j, j ≠ k → b j = a j}
  have hc : IsClosed {b : X n | ∀ j, j ≠ k → b j = a j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (continuous_apply j) continuous_const
  have hS : IsCompact S := (compact_level h0bot hkbot hB3 hx0 hbdd).inter_right hc
  have hne : S.Nonempty := ⟨a, ha, fun _ _ => rfl⟩
  obtain ⟨b, hb, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne hS
    ((objective_lsc h0bot hkbot hB3).lowerSemicontinuousOn _)
  refine ⟨b, hb.1, hb.2, fun y => ?_⟩
  by_cases hy : Function.update a k y ∈ levelSet (fSum f0 fk) x0
  · exact hmin ⟨hy, fun j hj => Function.update_of_ne hj _ _⟩
  · exact hb.1.trans (le_of_lt (lt_of_not_ge hy))

lemma run_exists (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB3 : AssumptionB3 f0 fk) {x0 : X n} (hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0)) (s : ℕ → Fin N) :
    ∃ x : ℕ → X n, x 0 = x0 ∧ IsBCDRun (fSum f0 fk) s x := by
  classical
  let K := levelSet (fSum f0 fk) x0
  have hs : ∀ a : K, ∀ k : Fin N, ∃ b : K,
      (∀ j, j ≠ k → (b : X n) j = (a : X n) j) ∧
        ∀ y, fSum f0 fk b ≤ fSum f0 fk (Function.update (a : X n) k y) := by
    intro a k
    obtain ⟨b, hb, hchange, hmin⟩ := block_min_exists h0bot hkbot hB3 hx0 hbdd a.property k
    exact ⟨⟨b, hb⟩, hchange, hmin⟩
  choose step hstep using hs
  let u : ℕ → K := Nat.rec ⟨x0, show fSum f0 fk x0 ≤ fSum f0 fk x0 from le_rfl⟩ (fun r a => step a (s r))
  let v : ℕ → X n := fun r => (u r).val
  have hv0 : v 0 = x0 := rfl
  refine ⟨v, hv0, ?_⟩
  constructor
  · exact hx0
  · intro r
    exact hstep (u r) (s r)

lemma descent_gap_tendsto (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB3 : AssumptionB3 f0 fk) {x0 : X n} (hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0))
    {s : ℕ → Fin N} {x : ℕ → X n} (hinit : x 0 = x0) (hrun : IsBCDRun (fSum f0 fk) s x) :
    Tendsto (fun r => (fSum f0 fk (x r)).toReal - (fSum f0 fk (x (r+1))).toReal) atTop (𝓝 0) := by
  let f := fSum f0 fk
  have hK := compact_level h0bot hkbot hB3 hx0 hbdd
  have hlevel := run_level hinit hrun
  have hfin : ∀ r, f (x r) ≠ ⊤ := fun r => ne_top_of_le_ne_top hx0 (hlevel r)
  obtain ⟨z, hz, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (show (levelSet f x0).Nonempty from ⟨x0, show f x0 ≤ f x0 from le_rfl⟩) hK
    ((objective_lsc h0bot hkbot hB3).lowerSemicontinuousOn _)
  have ha : Antitone (fun r => (f (x r)).toReal) := antitone_nat_of_succ_le fun r =>
    EReal.toReal_le_toReal (run_descent hrun r) (objective_ne_bot h0bot hkbot _) (hfin r)
  have hl : BddBelow (Set.range fun r => (f (x r)).toReal) := by
    refine ⟨(f z).toReal, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact EReal.toReal_le_toReal (hmin (hlevel r)) (objective_ne_bot h0bot hkbot z) (hfin r)
  have ht := tendsto_atTop_ciInf ha hl
  have ht' := ht.comp (tendsto_add_atTop_nat 1)
  simpa using ht.sub ht'

end TsengHemivariateProof

open Filter Topology
open TsengBCD.Stationary TsengBCD.Hemivariate

namespace TsengHemivariateProof

lemma lsc_real_lower {Y : Type*} [TopologicalSpace Y] {f : Y → EReal}
    {a : ℕ → Y} {z : Y} (hf : LowerSemicontinuousAt f z)
    (ha : Tendsto a atTop (𝓝 z))
    (hfin : ∀ m, f (a m) ≠ ⊤ ∧ f (a m) ≠ ⊥)
    (hz : f z ≠ ⊤ ∧ f z ≠ ⊥) {c : ℝ} (hc : c < (f z).toReal) :
    ∀ᶠ m in atTop, c < (f (a m)).toReal := by
  have hce : (c : EReal) < f z := by
    rw [← EReal.coe_toReal hz.1 hz.2]
    exact EReal.coe_lt_coe_iff.mpr hc
  filter_upwards [ha.eventually (hf c hce)] with m hm
  rw [← EReal.coe_toReal (hfin m).1 (hfin m).2] at hm
  exact EReal.coe_lt_coe_iff.mp hm

lemma lsc_real_le_limit {Y : Type*} [TopologicalSpace Y] {f : Y → EReal}
    {a : ℕ → Y} {z : Y} (hf : LowerSemicontinuousAt f z)
    (ha : Tendsto a atTop (𝓝 z))
    (hfin : ∀ m, f (a m) ≠ ⊤ ∧ f (a m) ≠ ⊥)
    (hz : f z ≠ ⊤ ∧ f z ≠ ⊥) {c : ℝ}
    (hc : Tendsto (fun m => (f (a m)).toReal) atTop (𝓝 c)) :
    (f z).toReal ≤ c := by
  by_contra! h
  have hl := lsc_real_lower hf ha hfin hz (show (c + (f z).toReal) / 2 < (f z).toReal by linarith)
  have he : (c + (f z).toReal) / 2 ≤ c :=
    ge_of_tendsto hc (hl.mono fun _ hm => hm.le)
  linarith

lemma lsc_real_tendsto_of_upper {Y : Type*} [TopologicalSpace Y] {f : Y → EReal}
    {a : ℕ → Y} {z : Y} (hf : LowerSemicontinuousAt f z)
    (ha : Tendsto a atTop (𝓝 z))
    (hfin : ∀ m, f (a m) ≠ ⊤ ∧ f (a m) ≠ ⊥)
    (hz : f z ≠ ⊤ ∧ f z ≠ ⊥) {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 (f z).toReal))
    (hle : ∀ᶠ m in atTop, (f (a m)).toReal ≤ u m) :
    Tendsto (fun m => (f (a m)).toReal) atTop (𝓝 (f z).toReal) := by
  refine tendsto_order.mpr ⟨fun c hc => lsc_real_lower hf ha hfin hz hc, ?_⟩
  intro c hc
  filter_upwards [hle, (tendsto_order.mp hu).2 c hc] with m hm hm'
  exact lt_of_le_of_lt hm hm'

variable {N : ℕ} {n : Fin N → ℕ}
variable {f0 : X n → EReal}
variable {fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal}

lemma comparison_domain (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {a : ℕ → X n} {z : X n} (ha : Tendsto a atTop (𝓝 z))
    (hdom : ∀ m, a m ∈ dom f0) (k : Fin N) (y : EuclideanSpace ℝ (Fin (n k)))
    (hy : Function.update z k y ∈ dom f0) :
    ∀ᶠ m in atTop, Function.update (a m) k y ∈ dom f0 := by
  classical
  rcases hC with hC | ⟨Y, hY⟩
  · exact (ha.update k tendsto_const_nhds).eventually (hC.1.mem_nhds hy)
  · apply Eventually.of_forall
    intro m
    have hm := hdom m
    rw [hY] at hm hy ⊢
    intro j hj
    by_cases hjk : j = k
    · subst j
      simpa using hy k (Set.mem_univ k)
    · simpa [Function.update_of_ne hjk] using hm j hj

lemma comparison_f0_tendsto (hB1 : AssumptionB1 f0)
    (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {a : ℕ → X n} {z : X n} (ha : Tendsto a atTop (𝓝 z))
    (hdom : ∀ m, a m ∈ dom f0) (k : Fin N) (y : EuclideanSpace ℝ (Fin (n k)))
    (hy : Function.update z k y ∈ dom f0) :
    Tendsto (fun m => f0 (Function.update (a m) k y)) atTop
      (𝓝 (f0 (Function.update z k y))) := by
  have hc := ha.update k (tendsto_const_nhds (x := y))
  exact Filter.Tendsto.comp (hB1 _ hy)
    (tendsto_nhdsWithin_iff.mpr ⟨hc, comparison_domain hC ha hdom k y hy⟩)

lemma comparison_partial_tendsto
    (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB1 : AssumptionB1 f0) (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {a : ℕ → X n} {z : X n} (ha : Tendsto a atTop (𝓝 z))
    (hdom : ∀ m, a m ∈ dom f0) (k : Fin N) (y : EuclideanSpace ℝ (Fin (n k)))
    (hy0 : f0 (Function.update z k y) ≠ ⊤) (hyk : fk k y ≠ ⊤) :
    Tendsto (fun m => (partialObjective f0 fk k (Function.update (a m) k y)).toReal)
      atTop (𝓝 (partialObjective f0 fk k (Function.update z k y)).toReal) := by
  have hc := comparison_f0_tendsto hB1 hC ha hdom k y hy0
  have hadd : Tendsto (fun m => f0 (Function.update (a m) k y) + fk k y) atTop
      (𝓝 (f0 (Function.update z k y) + fk k y)) :=
    (EReal.continuousAt_add (Or.inl hy0) (Or.inl (h0bot _))).tendsto.comp
      (hc.prodMk_nhds tendsto_const_nhds)
  have hr := (EReal.tendsto_toReal (EReal.add_ne_top hy0 hyk)
    (EReal.add_ne_bot_iff.mpr ⟨h0bot _, hkbot k y⟩)).comp hadd
  simpa only [partialObjective, Function.update_self, Function.comp_def] using hr

lemma comparison_partial_finite
    (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {a : ℕ → X n} {z : X n} (ha : Tendsto a atTop (𝓝 z))
    (hdom : ∀ m, a m ∈ dom f0) (k : Fin N) (y : EuclideanSpace ℝ (Fin (n k)))
    (hy0 : f0 (Function.update z k y) ≠ ⊤) (hyk : fk k y ≠ ⊤) :
    ∀ᶠ m in atTop, partialObjective f0 fk k (Function.update (a m) k y) ≠ ⊤ := by
  filter_upwards [comparison_domain hC ha hdom k y hy0] with m hm
  simpa only [partialObjective, Function.update_self] using EReal.add_ne_top hm hyk

end TsengHemivariateProof

open Filter Topology
open TsengBCD.Stationary TsengBCD.Hemivariate

namespace TsengHemivariateProof

variable {N : ℕ} {n : Fin N → ℕ}
variable {f0 : X n → EReal}
variable {fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal}

lemma pair_limit
    (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB : AssumptionB f0 fk) (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {x0 : X n} (hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0))
    {a b : ℕ → X n} {z w : X n} {k : Fin N}
    (hKa : ∀ m, a m ∈ levelSet (fSum f0 fk) x0)
    (hKb : ∀ m, b m ∈ levelSet (fSum f0 fk) x0)
    (hchange : ∀ m j, j ≠ k → b m j = a m j)
    (hmin : ∀ m y, fSum f0 fk (b m) ≤ fSum f0 fk (Function.update (a m) k y))
    (ha : Tendsto a atTop (𝓝 z)) (hb : Tendsto b atTop (𝓝 w))
    (hgap : Tendsto (fun m => (fSum f0 fk (a m)).toReal - (fSum f0 fk (b m)).toReal)
      atTop (𝓝 0)) :
    z = w ∧ ∀ y, fSum f0 fk z ≤ fSum f0 fk (Function.update z k y) := by
  classical
  have hK := compact_level h0bot hkbot hB.2.2 hx0 hbdd
  have hzK := hK.isClosed.mem_of_tendsto ha (Eventually.of_forall hKa)
  have hwK := hK.isClosed.mem_of_tendsto hb (Eventually.of_forall hKb)
  have hf (v : X n) (hv : v ∈ levelSet (fSum f0 fk) x0) : fSum f0 fk v ≠ ⊤ :=
    ne_top_of_le_ne_top hx0 hv
  have hp (v : X n) (hv : v ∈ levelSet (fSum f0 fk) x0) :
      partialObjective f0 fk k v ≠ ⊤ ∧ partialObjective f0 fk k v ≠ ⊥ := by
    exact ⟨EReal.add_ne_top (objective_finite h0bot hkbot (hf v hv)).1
      ((objective_finite h0bot hkbot (hf v hv)).2 k),
      EReal.add_ne_bot_iff.mpr ⟨h0bot v, hkbot k (v k)⟩⟩
  have hpb (v : X n) : partialObjective f0 fk k v ≠ ⊥ :=
    EReal.add_ne_bot_iff.mpr ⟨h0bot v, hkbot k (v k)⟩
  have hdom : ∀ m, a m ∈ dom f0 :=
    fun m => (objective_finite h0bot hkbot (hf _ (hKa m))).1
  have hoff : ∀ j, j ≠ k → w j = z j := by
    intro j hj
    have he : (fun m => b m j) = fun m => a m j := funext fun m => hchange m j hj
    have hb' := hb.apply_nhds j
    rw [he] at hb'
    exact tendsto_nhds_unique hb' (ha.apply_nhds j)
  have hw : Function.update z k (w k) = w := by
    funext j
    by_cases hj : j = k
    · subst j
      simp
    · simpa only [Function.update_of_ne hj] using (hoff j hj).symm
  have hminp (m : ℕ) (y : EuclideanSpace ℝ (Fin (n k))) :
      partialObjective f0 fk k (b m) ≤ partialObjective f0 fk k (Function.update (a m) k y) := by
    apply (block_le_iff_partial_le h0bot hkbot (hf _ (hKb m)) ?_).mp (hmin m y)
    intro j hj
    simpa only [Function.update_of_ne hj] using (hchange m j hj).symm
  have hwy0 : f0 (Function.update z k (w k)) ≠ ⊤ := by
    rw [hw]
    exact (objective_finite h0bot hkbot (hf _ hwK)).1
  have hwyk : fk k (w k) ≠ ⊤ := (objective_finite h0bot hkbot (hf _ hwK)).2 k
  have huw := comparison_partial_tendsto h0bot hkbot hB.1 hC ha hdom k (w k) hwy0 hwyk
  rw [hw] at huw
  have hbw : Tendsto (fun m => (partialObjective f0 fk k (b m)).toReal) atTop
      (𝓝 (partialObjective f0 fk k w).toReal) := by
    apply lsc_real_tendsto_of_upper (partial_lsc h0bot hkbot hB.2.2 k w) hb
      (fun m => hp _ (hKb m)) (hp _ hwK) huw
    filter_upwards [comparison_partial_finite hC ha hdom k (w k) hwy0 hwyk] with m hm
    exact EReal.toReal_le_toReal (hminp m (w k)) (hpb _) hm
  have hpmin : ∀ y, partialObjective f0 fk k w ≤ partialObjective f0 fk k (Function.update z k y) := by
    intro y
    by_cases hyt : partialObjective f0 fk k (Function.update z k y) = ⊤
    · simp only [hyt, le_top]
    have hfins : f0 (Function.update z k y) ≠ ⊤ ∧ fk k y ≠ ⊤ := by
      apply (EReal.add_ne_top_iff_ne_top₂ (h0bot _) (hkbot k y)).mp
      simpa only [partialObjective, Function.update_self] using hyt
    have huy := comparison_partial_tendsto h0bot hkbot hB.1 hC ha hdom k y hfins.1 hfins.2
    have hr : (partialObjective f0 fk k w).toReal ≤
        (partialObjective f0 fk k (Function.update z k y)).toReal := by
      apply le_of_tendsto_of_tendsto hbw huy
      filter_upwards [comparison_partial_finite hC ha hdom k y hfins.1 hfins.2] with m hm
      exact EReal.toReal_le_toReal (hminp m y) (hpb _) hm
    rw [← EReal.coe_toReal (hp _ hwK).1 (hpb _), ← EReal.coe_toReal hyt (hpb _)]
    exact EReal.coe_le_coe_iff.mpr hr
  have hegap : (fun m => (fSum f0 fk (a m)).toReal - (fSum f0 fk (b m)).toReal) =
      fun m => (partialObjective f0 fk k (a m)).toReal - (partialObjective f0 fk k (b m)).toReal := by
    funext m
    exact partial_difference h0bot hkbot (hf _ (hKa m)) (hf _ (hKb m)) (hchange m)
  rw [hegap] at hgap
  have haw : Tendsto (fun m => (partialObjective f0 fk k (a m)).toReal) atTop
      (𝓝 (partialObjective f0 fk k w).toReal) := by
    simpa only [sub_add_cancel, zero_add] using hgap.add hbw
  have hzwReal := lsc_real_le_limit (partial_lsc h0bot hkbot hB.2.2 k z) ha
    (fun m => hp _ (hKa m)) (hp _ hzK) haw
  have hzw : partialObjective f0 fk k z ≤ partialObjective f0 fk k w := by
    rw [← EReal.coe_toReal (hp _ hzK).1 (hpb _), ← EReal.coe_toReal (hp _ hwK).1 (hpb _)]
    exact EReal.coe_le_coe_iff.mpr hzwReal
  have hzm : ∀ y, fSum f0 fk z ≤ fSum f0 fk (Function.update z k y) := by
    intro y
    apply (block_le_iff_partial_le h0bot hkbot (hf _ hzK) ?_).mpr (hzw.trans (hpmin y))
    intro j hj
    exact Function.update_of_ne hj _ _
  have hwm : ∀ y, fSum f0 fk w ≤ fSum f0 fk (Function.update z k y) := by
    intro y
    apply (block_le_iff_partial_le h0bot hkbot (hf _ hwK) ?_).mpr (hpmin y)
    intro j hj
    simpa only [Function.update_of_ne hj] using (hoff j hj).symm
  have hcoord : z k = w k := by
    apply quasi_hemi_min_unique (hB.2.1 k z).1 (hB.2.1 k z).2
    · simpa using hf _ hzK
    · intro y
      simpa using hzm y
    · intro y
      simpa only [hw] using hwm y
  exact ⟨by simpa [← hcoord] using hw, hzm⟩

end TsengHemivariateProof

open Filter Topology
open TsengBCD.Stationary TsengBCD.Hemivariate

namespace TsengHemivariateProof

lemma constant_subsequence {I : Type*} [Finite I] (f : ℕ → I) :
    ∃ i, ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ m, f (r m) = i := by
  have hf : ∃ᶠ m in atTop, ∃ i, f m = i := Frequently.of_forall fun m => ⟨f m, rfl⟩
  obtain ⟨i, hi⟩ := Filter.frequently_exists.mp hf
  obtain ⟨r, hr, he⟩ := extraction_of_frequently_atTop hi
  exact ⟨i, r, hr, he⟩

variable {N : ℕ} {n : Fin N → ℕ}
variable {f0 : X n → EReal}
variable {fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal}

lemma successor_tendsto
    (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB : AssumptionB f0 fk) (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {x0 : X n} (hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0))
    {s : ℕ → Fin N} {x : ℕ → X n} (hinit : x 0 = x0)
    (hrun : IsBCDRun (fSum f0 fk) s x)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {z : X n}
    (hz : Tendsto (fun m => x (r m)) atTop (𝓝 z)) :
    Tendsto (fun m => x (r m + 1)) atTop (𝓝 z) := by
  have hK := compact_level h0bot hkbot hB.2.2 hx0 hbdd
  have hlevel := run_level hinit hrun
  have hgap := descent_gap_tendsto h0bot hkbot hB.2.2 hx0 hbdd hinit hrun
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨w, _, φ, hφ, hw⟩ := hK.tendsto_subseq (fun m => hlevel (r (ns m) + 1))
  obtain ⟨k, ψ, hψ, hk⟩ := constant_subsequence (fun m => s (r (ns (φ m))))
  let q : ℕ → ℕ := fun m => r (ns (φ (ψ m)))
  have hq : Tendsto q atTop atTop := hr.comp (hns.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  have hza : Tendsto (fun m => x (q m)) atTop (𝓝 z) :=
    hz.comp (hns.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  have hwb : Tendsto (fun m => x (q m + 1)) atTop (𝓝 w) := hw.comp hψ.tendsto_atTop
  have hblock : ∀ m, s (q m) = k := hk
  have he := pair_limit h0bot hkbot hB hC hx0 hbdd
    (fun m => hlevel (q m)) (fun m => hlevel (q m + 1))
    (k := k) (fun m => by simpa only [hblock m] using (hrun.2 (q m)).1)
    (fun m => by rw [← hblock m]; exact (hrun.2 (q m)).2)
    hza hwb (hgap.comp hq)
  refine ⟨fun m => φ (ψ m), ?_⟩
  rw [he.1]
  exact hwb

lemma shifted_tendsto
    (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB : AssumptionB f0 fk) (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {x0 : X n} (hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0))
    {s : ℕ → Fin N} {x : ℕ → X n} (hinit : x 0 = x0)
    (hrun : IsBCDRun (fSum f0 fk) s x)
    {r : ℕ → ℕ} (hr : Tendsto r atTop atTop) {z : X n}
    (hz : Tendsto (fun m => x (r m)) atTop (𝓝 z)) (j : ℕ) :
    Tendsto (fun m => x (r m + j)) atTop (𝓝 z) := by
  induction j with
  | zero => simpa only [Nat.add_zero] using hz
  | succ j ih =>
    have hq := (tendsto_add_atTop_nat j).comp hr
    simpa only [Nat.add_assoc, Nat.succ_eq_add_one, Function.comp_def] using
      successor_tendsto h0bot hkbot hB hC hx0 hbdd hinit hrun hq ih

lemma cluster_coordMin
    (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB : AssumptionB f0 fk) (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    {x0 : X n} (hx0 : fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (levelSet (fSum f0 fk) x0))
    {s : ℕ → Fin N} {x : ℕ → X n} (hs : IsEssCyclic s)
    (hinit : x 0 = x0) (hrun : IsBCDRun (fSum f0 fk) s x)
    {z : X n} (hz : MapClusterPt z atTop x) : IsCoordMin (fSum f0 fk) z := by
  classical
  obtain ⟨r, hr, hzr⟩ := hz.tendsto_subseq
  have hz' : Tendsto (fun m => x (r m)) atTop (𝓝 z) := hzr
  have hlevel := run_level hinit hrun
  have hK := compact_level h0bot hkbot hB.2.2 hx0 hbdd
  have hzK := hK.isClosed.mem_of_tendsto hz' (Eventually.of_forall fun m => hlevel (r m))
  refine ⟨ne_top_of_le_ne_top hx0 hzK, ?_⟩
  intro k dk
  obtain ⟨T, _, hT⟩ := hs
  choose j hjT hjk using fun m => hT (r m) k
  let ix : ℕ → Fin T := fun m => ⟨j m, hjT m⟩
  obtain ⟨J, ψ, hψ, hJ⟩ := constant_subsequence ix
  let q : ℕ → ℕ := fun m => r (ψ m) + J.val
  have hq : Tendsto q atTop atTop := (tendsto_add_atTop_nat J.val).comp
    (hr.tendsto_atTop.comp hψ.tendsto_atTop)
  have hblock : ∀ m, s (q m) = k := by
    intro m
    have hval : j (ψ m) = J.val := congrArg Fin.val (hJ m)
    simpa only [q, hval] using hjk (ψ m)
  have ha : Tendsto (fun m => x (q m)) atTop (𝓝 z) :=
    (shifted_tendsto h0bot hkbot hB hC hx0 hbdd hinit hrun hr.tendsto_atTop hz' J.val).comp
      hψ.tendsto_atTop
  have hb : Tendsto (fun m => x (q m + 1)) atTop (𝓝 z) := by
    simpa only [q, Nat.add_assoc, Function.comp_def] using
      (shifted_tendsto h0bot hkbot hB hC hx0 hbdd hinit hrun hr.tendsto_atTop hz' (J.val + 1)).comp
        hψ.tendsto_atTop
  have hgap := (descent_gap_tendsto h0bot hkbot hB.2.2 hx0 hbdd hinit hrun).comp hq
  have he := pair_limit h0bot hkbot hB hC hx0 hbdd
    (fun m => hlevel (q m)) (fun m => hlevel (q m + 1))
    (k := k) (fun m => by simpa only [hblock m] using (hrun.2 (q m)).1)
    (fun m => by rw [← hblock m]; exact (hrun.2 (q m)).2) ha hb hgap
  have hup : z + Pi.single k dk = Function.update z k (z k + dk) := by
    funext i
    by_cases hi : i = k
    · subst i
      simp
    · simp [hi]
  rw [hup]
  exact he.2 (z k + dk)

end TsengHemivariateProof

namespace TsengBCD.Hemivariate

open Filter Topology

theorem theorem_5_1 {N : ℕ} [NeZero N] {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal)
    (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal)
    (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB : AssumptionB f0 fk) (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    (x0 : TsengBCD.Stationary.X n) (hx0 : TsengBCD.Stationary.fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (TsengBCD.Stationary.levelSet (TsengBCD.Stationary.fSum f0 fk) x0)) :
    (∀ s : ℕ → Fin N, ∃ x : ℕ → TsengBCD.Stationary.X n, x 0 = x0 ∧ TsengBCD.Stationary.IsBCDRun (TsengBCD.Stationary.fSum f0 fk) s x) ∧
      ∀ (s : ℕ → Fin N) (x : ℕ → TsengBCD.Stationary.X n), TsengBCD.Stationary.IsEssCyclic s → x 0 = x0 → TsengBCD.Stationary.IsBCDRun (TsengBCD.Stationary.fSum f0 fk) s x →
        Bornology.IsBounded (Set.range x) ∧
          ∀ z, MapClusterPt z atTop x → TsengBCD.Stationary.IsCoordMin (TsengBCD.Stationary.fSum f0 fk) z := by
  constructor
  · intro s
    exact TsengHemivariateProof.run_exists h0bot hkbot hB.2.2 hx0 hbdd s
  · intro s x hs hinit hrun
    refine ⟨hbdd.subset ?_, ?_⟩
    · rintro _ ⟨r, rfl⟩
      exact TsengHemivariateProof.run_level hinit hrun r
    · intro z hz
      exact TsengHemivariateProof.cluster_coordMin h0bot hkbot hB hC hx0 hbdd hs hinit hrun hz

end TsengBCD.Hemivariate

open TsengBCD.Hemivariate

theorem solution {N : ℕ} [NeZero N] {n : Fin N → ℕ} (f0 : TsengBCD.Stationary.X n → EReal)
    (fk : (k : Fin N) → EuclideanSpace ℝ (Fin (n k)) → EReal)
    (h0bot : ∀ x, f0 x ≠ ⊥) (hkbot : ∀ k y, fk k y ≠ ⊥)
    (hB : AssumptionB f0 fk) (hC : AssumptionC1 f0 ∨ AssumptionC2 f0)
    (x0 : TsengBCD.Stationary.X n) (hx0 : TsengBCD.Stationary.fSum f0 fk x0 ≠ ⊤)
    (hbdd : Bornology.IsBounded (TsengBCD.Stationary.levelSet (TsengBCD.Stationary.fSum f0 fk) x0)) :
    (∀ s : ℕ → Fin N, ∃ x : ℕ → TsengBCD.Stationary.X n, x 0 = x0 ∧ TsengBCD.Stationary.IsBCDRun (TsengBCD.Stationary.fSum f0 fk) s x) ∧
      ∀ (s : ℕ → Fin N) (x : ℕ → TsengBCD.Stationary.X n), TsengBCD.Stationary.IsEssCyclic s → x 0 = x0 → TsengBCD.Stationary.IsBCDRun (TsengBCD.Stationary.fSum f0 fk) s x →
        Bornology.IsBounded (Set.range x) ∧
          ∀ z, MapClusterPt z atTop x → TsengBCD.Stationary.IsCoordMin (TsengBCD.Stationary.fSum f0 fk) z := by
  exact TsengBCD.Hemivariate.theorem_5_1 f0 fk h0bot hkbot hB hC x0 hx0 hbdd
