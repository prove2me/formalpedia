-- Prove2me | solution 1 for PoAIndep.Topology.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T10:29:29.397734+00:00
-- url     : https://prove2.me/submissions/57dee92b-16d9-4a08-9548-01583db50196

/-
SPDX-License-Identifier: Apache-2.0
Original standalone Lean proof of the complete topology-independent price of anarchy theorem.
Mathematical source: Tim Roughgarden, The Price of Anarchy is Independent of the Network
Topology, author manuscript December 23, 2002, Theorem 4.2 and Sections 2–4.1.
Native Prove2Me definitions are imported unchanged. No accepted proof source is copied.
Both arbitrary-network upper and literal two-link lower clauses are proved. The proof derives
Nash-to-VI from finite deviations and uses an interior compact minimum for the scalar bound.
-/
import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

-- BEGIN Foundation

-- END Foundation

-- BEGIN Scalar
namespace PoATopologyProof

open PoAIndep.Topology Set

lemma admissible_denominator_pos {ℓ : ℝ → ℝ} (hℓ : IsLatency ℓ)
    {r lam : ℝ} (hr : 0 < r) (hp : 0 < ℓ r) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    0 < lam * (ℓ (lam * r) / ℓ r) + (1 - lam) := by
  have hn : 0 ≤ lam * (ℓ (lam * r) / ℓ r) :=
    mul_nonneg hlam.1 (div_nonneg (hℓ.1 _ (mul_nonneg hlam.1 hr.le)) hp.le)
  by_cases he : lam = 1
  · simp [he, ne_of_gt hp]
  · have hlt : lam < 1 := lt_of_le_of_ne hlam.2 he
    linarith

lemma interior_minimizer {ℓ : ℝ → ℝ} (hℓ : IsLatency ℓ) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ Ioo (0 : ℝ) r,
      IsMinOn (fun y => y * ℓ y - y * ℓ r) (Ici 0) z := by
  let q : ℝ → ℝ := fun y => y * ℓ y - y * ℓ r
  have hcont : ContinuousOn q (Icc 0 r) := by
    exact (continuousOn_id.mul
      (hℓ.2.1.continuousOn.mono (fun _ hy => hy.1))).sub
        (continuousOn_id.mul continuousOn_const)
  obtain ⟨z, hz, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) r).Nonempty from ⟨0, by simp [hr.le]⟩) hcont
  have hzero : q 0 = 0 := by simp [q]
  have hrzero : q r = 0 := by simp [q]
  have hnonpos (y : ℝ) (hy : y ∈ Icc 0 r) : q y ≤ 0 := by
    dsimp [q]
    exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left
      (hℓ.2.2 hy.1 hr.le hy.2) hy.1)
  have houtside (y : ℝ) (hy : r ≤ y) : 0 ≤ q y := by
    dsimp [q]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (hℓ.2.2 hr.le (hr.le.trans hy) hy) (hr.le.trans hy))
  have hglobal : IsMinOn q (Ici 0) z := by
    intro y hy
    by_cases hyr : y ≤ r
    · exact hmin ⟨hy, hyr⟩
    · exact (hnonpos z hz).trans (houtside y (le_of_not_ge hyr))
  by_cases hneg : q z < 0
  · refine ⟨z, ⟨?_, ?_⟩, hglobal⟩
    · by_contra hn
      have he : z = 0 := le_antisymm (le_of_not_gt hn) hz.1
      rw [he, hzero] at hneg
      exact (lt_irrefl 0 hneg)
    · by_contra hn
      have he : z = r := le_antisymm hz.2 (le_of_not_gt hn)
      rw [he, hrzero] at hneg
      exact (lt_irrefl 0 hneg)
  · have hz0 : q z = 0 := le_antisymm (hnonpos z hz) (le_of_not_gt hneg)
    have hmid : r / 2 ∈ Icc (0 : ℝ) r := ⟨by linarith, by linarith⟩
    have hmid0 : q (r / 2) = 0 := by
      have hh := hmin hmid
      rw [hz0] at hh
      exact le_antisymm (hnonpos _ hmid) hh
    refine ⟨r / 2, ⟨by linarith, by linarith⟩, ?_⟩
    intro y hy
    have hh := hglobal hy
    change q (r / 2) ≤ q y
    rwa [hmid0, ← hz0]

lemma scalar_support {ℓ : ℝ → ℝ} (hℓ : IsLatency ℓ) {r : ℝ} (hr : 0 < r) :
    ∃ lam ∈ Icc (0 : ℝ) 1,
      marginalCost ℓ (lam * r) = ℓ r ∧
        ∀ y : ℝ, 0 ≤ y →
          lam * r * ℓ (lam * r) + (y - lam * r) * ℓ r ≤ y * ℓ y := by
  obtain ⟨z, hz, hmin⟩ := interior_minimizer hℓ hr
  have hnhds : Ici (0 : ℝ) ∈ nhds z := Ici_mem_nhds hz.1
  have hd : DifferentiableAt ℝ ℓ z := (hℓ.2.1 z hz.1.le).differentiableAt hnhds
  have hprod := (hasDerivAt_id' z).fun_mul hd.hasDerivAt
  have hq := hprod.fun_sub ((hasDerivAt_id' z).mul_const (ℓ r))
  have hder := (hmin.isLocalMin hnhds).hasDerivAt_eq_zero hq
  have hmarg : marginalCost ℓ z = ℓ r := by
    unfold marginalCost
    have hv : derivWithin (fun y => y * ℓ y) (Ici 0) z = ℓ z + z * deriv ℓ z := by
      simpa using hprod.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 z hz.1.le)
    rw [hv]
    simpa using sub_eq_zero.mp hder
  have hzr : (z / r) * r = z := div_mul_cancel₀ z (ne_of_gt hr)
  refine ⟨z / r, ⟨div_nonneg hz.1.le hr.le, (div_le_one hr).mpr hz.2.le⟩, ?_, ?_⟩
  · simpa [hzr] using hmarg
  · intro y hy
    have hh := hmin hy
    change z * ℓ z - z * ℓ r ≤ y * ℓ y - y * ℓ r at hh
    rw [hzr]
    nlinarith

end PoATopologyProof
-- END Scalar

-- BEGIN AnarchyBound
namespace PoATopologyProof

open PoAIndep.Topology Set
open scoped ENNReal

lemma witness_le_anarchy {L : Set (ℝ → ℝ)} {ℓ : ℝ → ℝ} (hmem : ℓ ∈ L)
    {r lam : ℝ} (hr : 0 < r) (hp : 0 < ℓ r) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (hm : marginalCost ℓ (lam * r) = ℓ r) :
    ENNReal.ofReal ((lam * (ℓ (lam * r) / ℓ r) + (1 - lam))⁻¹) ≤
      anarchyValue L := by
  unfold anarchyValue anarchyValueFn
  exact le_iSup_of_le ℓ (le_iSup_of_le hmem (le_iSup_of_le r
    (le_iSup_of_le hr (le_iSup_of_le hp (le_iSup_of_le lam
      (le_iSup_of_le hlam (le_iSup_of_le hm le_rfl)))))))

lemma one_le_anarchy {L : Set (ℝ → ℝ)} (hc : ContainsConstants L) :
    1 ≤ anarchyValue L := by
  have hm : marginalCost (fun _ : ℝ => (1 : ℝ)) ((1 / 2 : ℝ) * 1) = 1 := by
    unfold marginalCost
    simpa using ((hasDerivAt_id' (1 / 2 : ℝ)).mul_const (1 : ℝ)).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ici 0 (1 / 2) (by norm_num))
  have hh := witness_le_anarchy (hc 1 (by norm_num)) (r := 1) (lam := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) hm
  norm_num at hh ⊢
  exact hh

lemma anarchy_toReal_pos {L : Set (ℝ → ℝ)} (hc : ContainsConstants L)
    (hA : anarchyValue L ≠ ∞) : 0 < (anarchyValue L).toReal := by
  have hh := ENNReal.toReal_mono hA (one_le_anarchy hc)
  norm_num at hh
  linarith

lemma denominator_lower {L : Set (ℝ → ℝ)} (hc : ContainsConstants L)
    (hA : anarchyValue L ≠ ∞) {ℓ : ℝ → ℝ} (hmem : ℓ ∈ L) (hℓ : IsLatency ℓ)
    {r lam : ℝ} (hr : 0 < r) (hp : 0 < ℓ r) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (hm : marginalCost ℓ (lam * r) = ℓ r) :
    (anarchyValue L).toReal⁻¹ ≤ lam * (ℓ (lam * r) / ℓ r) + (1 - lam) := by
  have hD := admissible_denominator_pos hℓ hr hp hlam
  have hh := witness_le_anarchy hmem hr hp hlam hm
  rw [ENNReal.ofReal_le_iff_le_toReal hA] at hh
  exact (inv_le_comm₀ hD (anarchy_toReal_pos hc hA)).mp hh

lemma scalar_anarchy_bound {L : Set (ℝ → ℝ)} (hc : ContainsConstants L)
    (hA : anarchyValue L ≠ ∞) {ℓ : ℝ → ℝ} (hmem : ℓ ∈ L) (hℓ : IsLatency ℓ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (anarchyValue L).toReal⁻¹ * x * ℓ x + (y - x) * ℓ x ≤ y * ℓ y := by
  by_cases hx0 : x = 0
  · simp only [hx0, mul_zero, zero_mul, sub_zero, zero_add]
    exact mul_le_mul_of_nonneg_left (hℓ.2.2 (by simp) hy hy) hy
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  by_cases hl0 : ℓ x = 0
  · simp only [hl0, mul_zero, zero_add]
    exact mul_nonneg hy (hℓ.1 y hy)
  have hlp : 0 < ℓ x := lt_of_le_of_ne (hℓ.1 x hx) (Ne.symm hl0)
  obtain ⟨lam, hlam, hm, hs⟩ := scalar_support hℓ hxp
  have hD := denominator_lower hc hA hmem hℓ hxp hlp hlam hm
  have hmul := mul_le_mul_of_nonneg_right hD (mul_nonneg hx hlp.le)
  have halg :
      (lam * (ℓ (lam * x) / ℓ x) + (1 - lam)) * (x * ℓ x) + (y - x) * ℓ x =
        lam * x * ℓ (lam * x) + (y - lam * x) * ℓ x := by
    calc
      _ = lam * x * ((ℓ (lam * x) / ℓ x) * ℓ x) +
          (1 - lam) * x * ℓ x + (y - x) * ℓ x := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hl0]; ring
  have hh := hs y hy
  rw [← halg] at hh
  nlinarith

end PoATopologyProof
-- END AnarchyBound

-- BEGIN FlowAlgebra
open scoped BigOperators
open PoAIndep.Topology

namespace PoATopologyProof

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] in
 theorem simplePath_nodup {src tgt : E → V} {P : List E} {u v : V}
    (h : IsSimplePath src tgt P u v) : P.Nodup :=
  (List.nodup_cons.mp h.2.2.2.2).2.of_map _

 theorem edgeFlow_nonneg (I : Instance V E) {f : Flow I} (hf : IsFlow I f) (e : E) :
    0 ≤ edgeFlow I f e := by
  unfold edgeFlow Finsupp.sum
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun P _ => by
    dsimp only
    split_ifs
    · exact (hf i).1 P
    · rfl

 theorem pathLatency_eq_sum (I : Instance V E) (f : Flow I) {P : List E}
    (hP : P.Nodup) :
    pathLatency I f P = ∑ e, if e ∈ P then I.ℓ e (edgeFlow I f e) else 0 := by
  classical
  unfold pathLatency
  rw [← List.sum_toFinset _ hP]
  rw [← Finset.sum_filter]
  congr 1
  ext e
  simp


 theorem cross_cost_eq (I : Instance V E) (f : Flow I) {g : Flow I} (hg : IsFlow I g) :
    (∑ i, (g i).sum (fun P x => pathLatency I f P * x)) =
      ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I g e := by
  classical
  unfold edgeFlow
  simp only [Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  rw [pathLatency_eq_sum I f (simplePath_nodup ((hg i).2 P hP)), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all [edgeFlow, Finsupp.sum]

 theorem cost_eq_sum_edges (I : Instance V E) {f : Flow I} (hf : IsFlow I f) :
    cost I f = ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I f e :=
  cross_cost_eq I f hf

 theorem edgeFlow_update (I : Instance V E) (f : Flow I) (i : Fin I.k)
    (P Q : List E) (δ : ℝ) (e : E) :
    edgeFlow I (Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ)) e =
      edgeFlow I f e - (if e ∈ P then δ else 0) + (if e ∈ Q then δ else 0) := by
  classical
  have hadd (a b : List E →₀ ℝ) :
      (a + b).sum (fun R x => if e ∈ R then x else 0) =
        a.sum (fun R x => if e ∈ R then x else 0) +
        b.sum (fun R x => if e ∈ R then x else 0) := by
    apply Finsupp.sum_add_index' <;> intros <;> split_ifs <;> simp
  have hsub (a b : List E →₀ ℝ) :
      (a - b).sum (fun R x => if e ∈ R then x else 0) =
        a.sum (fun R x => if e ∈ R then x else 0) -
        b.sum (fun R x => if e ∈ R then x else 0) := by
    apply Finsupp.sum_sub_index
    intros
    split_ifs <;> simp
  unfold edgeFlow
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hh : (∑ j ∈ Finset.univ.erase i,
      (Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ) j).sum
        (fun R x => if e ∈ R then x else 0)) =
      ∑ j ∈ Finset.univ.erase i, (f j).sum (fun R x => if e ∈ R then x else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hh, Function.update_self, hadd, hsub]
  simp only [Finsupp.sum_single_index, ite_self]
  ring

 theorem update_nonneg (I : Instance V E) {f : Flow I} (hf : IsFlow I f)
    (i : Fin I.k) (P Q : List E) {δ : ℝ} (hδ : 0 ≤ δ) (hle : δ ≤ f i P) :
    ∀ j R, 0 ≤ (Function.update f i (f i - Finsupp.single P δ + Finsupp.single Q δ) j) R := by
  classical
  intro j R
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply]
    have hR := (hf i).1 R
    split_ifs <;> subst_vars <;> linarith
  · rw [Function.update_of_ne hji]
    exact (hf j).1 R

 theorem edgeFlow_nonneg_of_pointwise (I : Instance V E) {f : Flow I}
    (hf : ∀ i P, 0 ≤ f i P) (e : E) : 0 ≤ edgeFlow I f e := by
  unfold edgeFlow Finsupp.sum
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun P _ => by
    dsimp only
    split_ifs
    · exact hf i P
    · rfl

end PoATopologyProof
-- END FlowAlgebra

-- BEGIN FlowVI
open scoped BigOperators Topology
open Filter PoAIndep.Topology

namespace PoATopologyProof

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

 theorem nash_shortest (I : Instance V E) {f : Flow I} (hf : IsFlow I f)
    (hn : IsNashFlow I f) (i : Fin I.k) (P Q : List E)
    (hP : IsSimplePath I.src I.tgt P (I.s i) (I.t i))
    (hQ : IsSimplePath I.src I.tgt Q (I.s i) (I.t i)) (hpos : 0 < f i P) :
    pathLatency I f P ≤ pathLatency I f Q := by
  classical
  let δ : ℕ → ℝ := fun n => f i P / ((n : ℝ) + 1)
  have hdpos (n : ℕ) : 0 < δ n := div_pos hpos (by positivity)
  have hdle (n : ℕ) : δ n ≤ f i P := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hd : Tendsto δ atTop (𝓝 0) := by
    simpa [δ, div_eq_mul_inv] using
      (tendsto_const_nhds (x := f i P)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let u : ℕ → Flow I := fun n =>
    Function.update f i (f i - Finsupp.single P (δ n) + Finsupp.single Q (δ n))
  have he (e : E) : Tendsto (fun n => edgeFlow I (u n) e) atTop
      (𝓝[Set.Ici 0] edgeFlow I f e) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simp_rw [u, edgeFlow_update]
      have hp : Tendsto (fun n => if e ∈ P then δ n else 0) atTop (𝓝 0) := by
        split_ifs <;> first | exact hd | exact tendsto_const_nhds
      have hq : Tendsto (fun n => if e ∈ Q then δ n else 0) atTop (𝓝 0) := by
        split_ifs <;> first | exact hd | exact tendsto_const_nhds
      simpa using (tendsto_const_nhds.sub hp).add hq
    · exact Filter.Eventually.of_forall fun n =>
        edgeFlow_nonneg_of_pointwise I (update_nonneg I hf i P Q (hdpos n).le (hdle n)) e
  have hl (e : E) : Tendsto (fun n => I.ℓ e (edgeFlow I (u n) e)) atTop
      (𝓝 (I.ℓ e (edgeFlow I f e))) :=
    ((I.latency e).2.1.continuousOn _ (edgeFlow_nonneg I hf e)).tendsto.comp (he e)
  have hpath : Tendsto (fun n => pathLatency I (u n) Q) atTop (𝓝 (pathLatency I f Q)) := by
    simp_rw [pathLatency_eq_sum _ _ (simplePath_nodup hQ)]
    apply tendsto_finsetSum
    intro e _
    split_ifs <;> first | exact hl e | exact tendsto_const_nhds
  exact ge_of_tendsto hpath (Filter.Eventually.of_forall fun n =>
    hn i P Q hP hQ hpos (δ n) ⟨hdpos n, hdle n⟩)

 theorem variational_inequality (I : Instance V E) {f g : Flow I}
    (hf : IsFlow I f) (hff : IsFeasible I f) (hn : IsNashFlow I f)
    (hg : IsFlow I g) (hgf : IsFeasible I g) :
    cost I f ≤ ∑ e, I.ℓ e (edgeFlow I f e) * edgeFlow I g e := by
  classical
  rw [← cross_cost_eq I f hg]
  unfold cost
  apply Finset.sum_le_sum
  intro i _
  have hex : ∃ P ∈ (f i).support, 0 < f i P := by
    have hsum : 0 < ∑ P ∈ (f i).support, f i P := by
      change 0 < (f i).sum (fun _ x => x)
      rw [hff i]
      exact I.r_pos i
    exact (Finset.sum_pos_iff_of_nonneg (fun P _ => (hf i).1 P)).mp hsum
  obtain ⟨P, hPm, hPpos⟩ := hex
  have hP := (hf i).2 P hPm
  have hcost : (f i).sum (fun Q x => pathLatency I f Q * x) =
      pathLatency I f P * I.r i := by
    rw [← hff i]
    unfold Finsupp.sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q hQm
    have hQpos : 0 < f i Q := lt_of_le_of_ne ((hf i).1 Q)
      (Ne.symm (Finsupp.mem_support_iff.mp hQm))
    have hQ := (hf i).2 Q hQm
    have heq := le_antisymm (nash_shortest I hf hn i Q P hQ hP hQpos)
      (nash_shortest I hf hn i P Q hP hQ hPpos)
    dsimp only
    rw [heq]
  rw [hcost, ← hgf i]
  unfold Finsupp.sum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro Q hQm
  exact mul_le_mul_of_nonneg_right
    (nash_shortest I hf hn i P Q hP ((hg i).2 Q hQm) hPpos) ((hg i).1 Q)

end PoATopologyProof
-- END FlowVI

-- BEGIN TwoLink
open scoped BigOperators ENNReal
open PoAIndep.Topology

namespace PoATopologyProof

 theorem parallel_path_singleton {P : List (Fin 2)}
    (h : IsSimplePath (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => 1) P 0 1) :
    ∃ e, P = [e] := by
  cases P with
  | nil => exact False.elim (h.1 rfl)
  | cons e P =>
    cases P with
    | nil => exact ⟨e, rfl⟩
    | cons e' P =>
      have hh := (List.isChain_cons_cons.mp h.2.1).1
      norm_num at hh

 theorem constant_latency {c : ℝ} (hc : 0 ≤ c) : IsLatency (fun _ : ℝ => c) :=
  ⟨fun _ _ => hc, differentiableOn_const _, fun _ _ _ _ _ => le_rfl⟩

 noncomputable def pairLatency (ℓ : ℝ → ℝ) (r : ℝ) : Fin 2 → ℝ → ℝ :=
  fun e => if e = 0 then ℓ else fun _ => ℓ r

 theorem pairLatency_valid {ℓ : ℝ → ℝ} (hℓ : IsLatency ℓ) {r : ℝ} (hr : 0 < r) :
    ∀ e, IsLatency (pairLatency ℓ r e) := by
  intro e
  unfold pairLatency
  split_ifs
  · exact hℓ
  · exact constant_latency (hℓ.1 _ hr.le)

 noncomputable def pairFlow (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ)
    (hℓ : ∀ e, IsLatency (ℓ e)) (a b : ℝ) : Flow (twoLink r hr ℓ hℓ) :=
  fun _ => Finsupp.single [0] a + Finsupp.single [1] b

 theorem pairFlow_valid (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ)
    (hℓ : ∀ e, IsLatency (ℓ e)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsFlow (twoLink r hr ℓ hℓ) (pairFlow r hr ℓ hℓ a b) := by
  intro i
  constructor
  · intro P
    simp only [pairFlow, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> linarith
  · intro P hP
    have hm := Finsupp.mem_support_iff.mp hP
    by_cases h0 : P = [0]
    · subst P
      exact isSimplePath_singleton _
    by_cases h1 : P = [1]
    · subst P
      exact isSimplePath_singleton _
    simp [pairFlow, h0, h1] at hm

 theorem pairFlow_feasible (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ)
    (hℓ : ∀ e, IsLatency (ℓ e)) {a b : ℝ} (hab : a + b = r) :
    IsFeasible (twoLink r hr ℓ hℓ) (pairFlow r hr ℓ hℓ a b) := by
  intro i
  simpa [pairFlow, Finsupp.sum_add_index, twoLink, parallelLinks] using hab

 theorem pairFlow_edge (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ)
    (hℓ : ∀ e, IsLatency (ℓ e)) (a b : ℝ) (e : Fin 2) :
    edgeFlow (twoLink r hr ℓ hℓ) (pairFlow r hr ℓ hℓ a b) e =
      if e = 0 then a else b := by
  change (∑ _i : Fin 1, ((Finsupp.single [0] a + Finsupp.single [1] b : List (Fin 2) →₀ ℝ).sum
    (fun P x => if e ∈ P then x else 0))) = _
  rw [Fin.sum_univ_one, Finsupp.sum_add_index' (fun _ => by split_ifs <;> rfl)
    (fun _ _ _ => by split_ifs <;> simp)]
  simp only [Finsupp.sum_single_index, ite_self]
  fin_cases e <;> simp


 theorem pairFlow_cost (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ)
    (hℓ : ∀ e, IsLatency (ℓ e)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    cost (twoLink r hr ℓ hℓ) (pairFlow r hr ℓ hℓ a b) = ℓ 0 a * a + ℓ 1 b * b := by
  rw [cost_eq_sum_edges _ (pairFlow_valid r hr ℓ hℓ ha hb)]
  simp only [Fin.sum_univ_two, pairFlow_edge]
  norm_num [twoLink, parallelLinks]

 theorem pigou_nash {ℓ : ℝ → ℝ} (hℓ : IsLatency ℓ) {r : ℝ} (hr : 0 < r) :
    IsNashFlow (twoLink r hr (pairLatency ℓ r) (pairLatency_valid hℓ hr))
      (pairFlow r hr (pairLatency ℓ r) (pairLatency_valid hℓ hr) r 0) := by
  intro i P Q hP hQ hpos δ hδ
  have _ := hδ
  obtain ⟨e, rfl⟩ := parallel_path_singleton hP
  obtain ⟨e', rfl⟩ := parallel_path_singleton hQ
  have he : e = 0 := by
    fin_cases e
    · rfl
    · simp [pairFlow] at hpos
  subst e
  simp only [pathLatency, List.map_singleton, List.sum_singleton]
  rw [edgeFlow_update, pairFlow_edge, pairFlow_edge]
  change (pairLatency ℓ r 0) r ≤ (pairLatency ℓ r e')
    ((if e' = 0 then r else 0) - (if e' ∈ [0] then δ else 0) +
      (if e' ∈ [e'] then δ else 0))
  fin_cases e' <;> simp [pairLatency]


end PoATopologyProof
-- END TwoLink

-- BEGIN Lower
open scoped ENNReal
open PoAIndep.Topology

namespace PoATopologyProof

 theorem two_link_lower (L : Set (ℝ → ℝ)) (hL : IsStandardClass L)
    (hc : ContainsConstants L) :
    ∀ b : ENNReal, b < anarchyValue L →
      ∃ (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ) (hℓ : ∀ e, IsLatency (ℓ e)),
        InClass (twoLink r hr ℓ hℓ) L ∧
          ∃ f g : Flow (twoLink r hr ℓ hℓ),
            IsFlow _ f ∧ IsFeasible _ f ∧ IsNashFlow _ f ∧
            IsFlow _ g ∧ IsFeasible _ g ∧ 0 < cost _ g ∧
            b < ENNReal.ofReal (cost _ f / cost _ g) := by
  intro b hb
  simp only [anarchyValue, anarchyValueFn, lt_iSup_iff] at hb
  obtain ⟨ℓ, hmem, r, hr, hp, lam, hlam, hder, hb⟩ := hb
  have _ := hder
  have hℓ := (hL.2 ℓ hmem).1
  let es := pairLatency ℓ r
  let hs := pairLatency_valid hℓ hr
  let I := twoLink r hr es hs
  let f := pairFlow r hr es hs r 0
  let g := pairFlow r hr es hs (lam * r) ((1 - lam) * r)
  have ha : 0 ≤ lam * r := mul_nonneg hlam.1 hr.le
  have hd : 0 ≤ (1 - lam) * r := mul_nonneg (sub_nonneg.mpr hlam.2) hr.le
  have hD := admissible_denominator_pos hℓ hr hp hlam
  have hf : IsFlow I f := pairFlow_valid r hr es hs hr.le (le_refl 0)
  have hg : IsFlow I g := pairFlow_valid r hr es hs ha hd
  have cf : cost I f = r * ℓ r := by
    rw [pairFlow_cost r hr es hs hr.le (le_refl 0)]
    simp [es, pairLatency, mul_comm]
  have cg : cost I g = r * ℓ r *
      (lam * (ℓ (lam * r) / ℓ r) + (1 - lam)) := by
    rw [pairFlow_cost r hr es hs ha hd]
    simp only [es, pairLatency]
    norm_num
    field_simp [ne_of_gt hp]
  refine ⟨r, hr, es, hs, ?_, f, g, hf, ?_, pigou_nash hℓ hr, hg, ?_, ?_, ?_⟩
  · intro e
    change (if e = 0 then ℓ else fun _ => ℓ r) ∈ L
    split_ifs
    · exact hmem
    · exact hc _ hp
  · exact pairFlow_feasible r hr es hs (by ring)
  · exact pairFlow_feasible r hr es hs (by ring)
  · rw [cg]
    exact mul_pos (mul_pos hr hp) hD
  · rw [cf, cg]
    have heq : r * ℓ r / (r * ℓ r *
        (lam * (ℓ (lam * r) / ℓ r) + (1 - lam))) =
        (lam * (ℓ (lam * r) / ℓ r) + (1 - lam))⁻¹ := by
      field_simp [ne_of_gt hr, ne_of_gt hp, ne_of_gt hD]
    rw [heq]
    exact hb

end PoATopologyProof
-- END Lower

-- BEGIN Upper
namespace PoATopologyProof

open PoAIndep.Topology
open scoped ENNReal

lemma network_upper {L : Set (ℝ → ℝ)} (hc : ContainsConstants L)
    {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (I : Instance V E) (hclass : InClass I L) (f g : Flow I)
    (hf : IsFlow I f) (hff : IsFeasible I f) (hn : IsNashFlow I f)
    (hg : IsFlow I g) (hgf : IsFeasible I g) (hcg : 0 < cost I g) :
    ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L := by
  by_cases hfin : anarchyValue L = ∞
  · simp [hfin]
  have hA := anarchy_toReal_pos hc hfin
  have hedge (e : E) :
      (anarchyValue L).toReal⁻¹ * (I.ℓ e (edgeFlow I f e) * edgeFlow I f e) +
          (I.ℓ e (edgeFlow I f e) * edgeFlow I g e -
            I.ℓ e (edgeFlow I f e) * edgeFlow I f e) ≤
        I.ℓ e (edgeFlow I g e) * edgeFlow I g e := by
    have hh := scalar_anarchy_bound hc hfin (hclass e) (I.latency e)
      (edgeFlow_nonneg I hf e) (edgeFlow_nonneg I hg e)
    nlinarith
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedge e)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← cost_eq_sum_edges I hf, ← cost_eq_sum_edges I hg] at hsum
  have hvi := variational_inequality I hf hff hn hg hgf
  have hbound : (anarchyValue L).toReal⁻¹ * cost I f ≤ cost I g := by linarith
  apply (ENNReal.ofReal_le_iff_le_toReal hfin).mpr
  apply (div_le_iff₀ hcg).mpr
  calc
    cost I f = (anarchyValue L).toReal *
        ((anarchyValue L).toReal⁻¹ * cost I f) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hA), one_mul]
    _ ≤ (anarchyValue L).toReal * cost I g := mul_le_mul_of_nonneg_left hbound hA.le

end PoATopologyProof
-- END Upper

-- BEGIN NativeRoot
namespace PoAIndep.Topology

theorem theorem_4_2 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hc : ContainsConstants L) :
    (∀ b : ENNReal, b < anarchyValue L →
      ∃ (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ) (hℓ : ∀ e, IsLatency (ℓ e)),
        InClass (twoLink r hr ℓ hℓ) L ∧
          ∃ f g : Flow (twoLink r hr ℓ hℓ),
            IsFlow _ f ∧ IsFeasible _ f ∧ IsNashFlow _ f ∧
            IsFlow _ g ∧ IsFeasible _ g ∧ 0 < cost _ g ∧
            b < ENNReal.ofReal (cost _ f / cost _ g)) ∧
    (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L) := by
  constructor
  · exact PoATopologyProof.two_link_lower L hL hc
  · intro V E _ _ _ _ I hclass f g hf hff hn hg hgf hcg
    exact PoATopologyProof.network_upper hc I hclass f g hf hff hn hg hgf hcg

end PoAIndep.Topology
-- END NativeRoot

open PoAIndep.Topology

theorem solution (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (hc : ContainsConstants L) :
    (∀ b : ENNReal, b < anarchyValue L →
      ∃ (r : ℝ) (hr : 0 < r) (ℓ : Fin 2 → ℝ → ℝ) (hℓ : ∀ e, IsLatency (ℓ e)),
        InClass (twoLink r hr ℓ hℓ) L ∧
          ∃ f g : Flow (twoLink r hr ℓ hℓ),
            IsFlow _ f ∧ IsFeasible _ f ∧ IsNashFlow _ f ∧
            IsFlow _ g ∧ IsFeasible _ g ∧ 0 < cost _ g ∧
            b < ENNReal.ofReal (cost _ f / cost _ g)) ∧
    (∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (I : Instance V E),
      InClass I L → ∀ f g : Flow I, IsFlow I f → IsFeasible I f → IsNashFlow I f →
        IsFlow I g → IsFeasible I g → 0 < cost I g →
          ENNReal.ofReal (cost I f / cost I g) ≤ anarchyValue L) :=
  PoAIndep.Topology.theorem_4_2 L hL hc
