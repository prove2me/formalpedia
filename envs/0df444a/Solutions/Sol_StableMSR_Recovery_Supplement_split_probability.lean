-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.split_probability
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-19T00:09:32.011207+00:00
-- url     : https://prove2.me/submissions/cabf41e9-d2a8-4dbd-abe4-2f5297a66517

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions
import Theorems.Thm_StableMSR_Recovery_Supplement_net_counts
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
open scoped Classical ENNReal
open StableMSR.Recovery
namespace GrowthAux

lemma metric_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : 0 ≤ d x y := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm]
  exact dist_nonneg

lemma metric_symm {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y : Point n) : d x y = d y x := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm]
  exact dist_comm x y

lemma metric_triangle {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) (x y z : Point n) : d x z ≤ d x y + d y z := by
  obtain ⟨m, hm⟩ := hd
  letI := m
  rw [← hm, ← hm, ← hm]
  exact dist_triangle x y z

lemma exists_center {n : ℕ} (d : Point n → Point n → ℝ)
    {C : Cluster n} (hC : C.Nonempty) : ∃ c, OptimalCenter d C c := by
  classical
  obtain ⟨c, hc, he⟩ := Finset.exists_mem_eq_inf' hC (eccentricity d C)
  refine ⟨c, hc, ?_⟩
  simp only [radius, dif_pos hC]
  exact he.symm

lemma distance_le_radius {n : ℕ} {d : Point n → Point n → ℝ}
    {C : Cluster n} {c x : Point n} (hc : OptimalCenter d C c) (hx : x ∈ C) :
    d c x ≤ radius d C := by
  have hC : C.Nonempty := ⟨c, hc.1⟩
  rw [← hc.2]
  simp only [eccentricity, dif_pos hC]
  exact Finset.le_sup' (d c) hx

lemma radius_nonneg {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : C.Nonempty) : 0 ≤ radius d C := by
  obtain ⟨c, hc⟩ := exists_center d hC
  exact (metric_nonneg hd c c).trans (distance_le_radius hc hc.1)

lemma radius_pos {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} (hC : 2 ≤ C.card) : 0 < radius d C := by
  classical
  have hne : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := exists_center d hne
  obtain ⟨y, hy, hyc⟩ := Finset.exists_mem_ne (by omega : 1 < C.card) c
  obtain ⟨m, hm⟩ := hd
  letI := m
  have hcy : 0 < d c y := by rw [← hm]; exact dist_pos.mpr hyc.symm
  exact hcy.trans_le (distance_le_radius hc hy)

lemma diameter_bound {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} {x y : Point n} (hx : x ∈ C) (hy : y ∈ C) :
    d x y ≤ 2 * radius d C := by
  obtain ⟨c, hc⟩ := exists_center d ⟨x, hx⟩
  have hcx := distance_le_radius hc hx
  have hcy := distance_le_radius hc hy
  have htri := metric_triangle hd x c y
  rw [metric_symm hd x c] at htri
  linarith

lemma radius_le_largest {n : ℕ} {d : Point n → Point n → ℝ}
    {O : Partition n} {C : Cluster n} (hC : C ∈ O) : radius d C ≤ largestRadius d O := by
  classical
  rw [largestRadius, dif_pos ⟨C, hC⟩]
  exact Finset.le_sup' _ hC

lemma largest_pos {n k : ℕ} {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {O : Partition n} (hO : Feasible Finset.univ k O) (hkn : k < n) :
    0 < largestRadius d O := by
  classical
  have hex : ∃ C ∈ O, 2 ≤ C.card := by
    by_contra hn
    have hc : ∀ C ∈ O, C.card ≤ 1 := by
      intro C hC
      by_contra hnC
      exact hn ⟨C, hC, by omega⟩
    have hsum : (∑ C ∈ O, C.card) ≤ O.card := by
      calc
        (∑ C ∈ O, C.card) ≤ ∑ C ∈ O, 1 := Finset.sum_le_sum hc
        _ = _ := by simp
    have hncard : (∑ C ∈ O, C.card) = n := by
      rw [← Finset.card_biUnion hO.2.2.1]
      change (O.biUnion id).card = n
      rw [hO.2.2.2]
      simp
    rw [hncard, hO.1] at hsum
    omega
  obtain ⟨C, hC, hC2⟩ := hex
  exact (radius_pos hd hC2).trans_le (radius_le_largest hC)

end GrowthAux
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

lemma order_probability {n : ℕ} (V : Cluster n) : IsProbabilityMeasure (orderLaw V) := by
  classical
  have total (l : List (List (Point n))) :
      ((l.map Measure.dirac).sum : Measure (List (Point n))) univ = (l.length : ℝ≥0∞) := by
    induction l with
    | nil => simp
    | cons a l ih => simp [Measure.add_apply,ih,add_comm]
  constructor
  simp only [orderLaw,Measure.smul_apply,smul_eq_mul,total]
  exact ENNReal.inv_mul_cancel (by simp [allOrders,List.length_permutations,Nat.factorial_ne_zero]) (by simp)

lemma radius_probability {L : ℝ} (pos : 0 < L) : IsProbabilityMeasure (radiusLaw L) := by
  constructor
  simp only [radiusLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ,Real.volume_Icc]
  rw [show L/8-L/16 = L/16 by ring]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top

lemma radius_half_open {L : ℝ} (pos : 0 < L) : radiusLaw L (Ico (L/16) (L/8)) = 1 := by
  rw [radiusLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr Ico_subset_Icc_self,Real.volume_Ico,show L/8-L/16 = L/16 by ring]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

def firstIn {n : ℕ} (T : Cluster n) (π : List (Point n)) :=
  π.find? (fun x => decide (x ∈ T))

private lemma swap_preserves {n : ℕ} (T : Cluster n) {a b : Point n}
    (ha : a ∈ T) (hb : b ∈ T) (z : Point n) : Equiv.swap a b z ∈ T ↔ z ∈ T := by
  by_cases za : z = a
  · subst z; simp [ha,hb]
  by_cases zb : z = b
  · subst z; simp [ha,hb]
  rw [Equiv.swap_apply_of_ne_of_ne za zb]

private lemma swapped_orders {n : ℕ} (V : Cluster n) {a b : Point n} (ha : a ∈ V) (hb : b ∈ V) :
    ((allOrders V).map (List.map (Equiv.swap a b))).Perm (allOrders V) := by
  unfold allOrders
  rw [List.map_permutations]
  apply List.Perm.permutations
  apply (List.perm_ext_iff_of_nodup ((V.sort_nodup _).map (Equiv.swap a b).injective) (V.sort_nodup _)).mpr
  intro x
  simp only [List.mem_map,Finset.mem_sort]
  constructor
  · rintro ⟨y,hy,rfl⟩; exact (swap_preserves V ha hb y).mpr hy
  · intro hx; exact ⟨_,(swap_preserves V ha hb x).mpr hx,Equiv.swap_apply_self ..⟩

lemma equally_often_first {n : ℕ} (V T : Cluster n) (sub : T ⊆ V) {a b : Point n} (ha : a ∈ T) (hb : b ∈ T) :
    (allOrders V).countP (fun π => decide (firstIn T π = some a)) =
    (allOrders V).countP (fun π => decide (firstIn T π = some b)) := by
  let s := Equiv.swap a b
  have pre : (fun z => decide (s z ∈ T)) = fun z => decide (z ∈ T) := by
    funext z; exact decide_eq_decide.mpr (swap_preserves T ha hb z)
  have mapFirst (π : List (Point n)) : firstIn T (π.map s) = (firstIn T π).map s := by
    simp only [firstIn,List.find?_map,Function.comp_def,pre]
  have repl : (fun π : List (Point n) => decide (firstIn T (π.map s) = some b)) =
      fun π => decide (firstIn T π = some a) := by
    funext π
    apply decide_eq_decide.mpr
    rw [mapFirst]
    cases h : firstIn T π with
    | none => simp
    | some x =>
      simp only [Option.map_some,Option.some.injEq]
      rw [show b = s a from (Equiv.swap_apply_left a b).symm]
      exact s.injective.eq_iff
  have h := (swapped_orders V (sub ha) (sub hb)).countP_eq (fun π => decide (firstIn T π = some b))
  simpa only [List.countP_map,Function.comp_def,←repl] using h

lemma total_first {n : ℕ} (V T : Cluster n) (sub : T ⊆ V) (ne : T.Nonempty) :
    ∑ a ∈ T, (allOrders V).countP (fun π => decide (firstIn T π = some a)) = (allOrders V).length := by
  have hit (π : List (Point n)) (hp : π ∈ allOrders V) : ∃ a ∈ T, firstIn T π = some a := by
    obtain ⟨z,hz⟩ := ne
    have zm : z ∈ π := (List.mem_permutations.mp hp).mem_iff.mpr (by simpa using sub hz)
    have yes : (firstIn T π).isSome := List.find?_isSome.mpr ⟨z,zm,by simpa using hz⟩
    obtain ⟨a,eq⟩ := Option.isSome_iff_exists.mp yes
    exact ⟨a,of_decide_eq_true (List.find?_some (p:=fun z => decide (z ∈ T)) eq),eq⟩
  suffices aux : ∀ l : List (List (Point n)), (∀ π ∈ l, ∃ a ∈ T, firstIn T π = some a) →
      ∑ a ∈ T, l.countP (fun π => decide (firstIn T π = some a)) = l.length from aux _ hit
  intro l
  induction l with
  | nil => simp
  | cons π l ih =>
    intro all
    obtain ⟨z,hz,eq⟩ := all π List.mem_cons_self
    have tail := ih (fun v hv => all v (by simp [hv]))
    simp only [List.countP_cons,decide_eq_true_eq,Finset.sum_add_distrib,tail,eq,Option.some.injEq,List.length_cons]
    simp [hz]

theorem order_mass {n : ℕ} (V : Cluster n) (P : List (Point n) → Prop) [DecidablePred P] :
    orderLaw V {π | P π} = ((allOrders V).length : ℝ≥0∞)⁻¹ *
      ((allOrders V).countP (fun π => decide (P π)) : ℝ≥0∞) := by
  have event : MeasurableSet {π | P π} := MeasurableSpace.measurableSet_top
  have mass (l : List (List (Point n))) : ((l.map Measure.dirac).sum : Measure (List (Point n))) {π | P π} =
      (l.countP (fun π => decide (P π)) : ℝ≥0∞) := by
    induction l with
    | nil => simp
    | cons π l ih =>
      by_cases h : P π <;> simp [Measure.add_apply,Measure.dirac_apply' _ event,ih,h,add_comm,
        Set.indicator_apply,List.countP_cons]
  exact (Measure.smul_apply ..).trans (congrArg (_ * ·) (mass _))

/-- Under the paper's actual multiset law on orders, each point in any
nonempty subset has probability exactly the reciprocal of the subset size
of appearing first among its members. -/
theorem order_first_probability {n : ℕ} (V T : Cluster n) (sub : T ⊆ V) (a : Point n) (ha : a ∈ T) :
    orderLaw V {π | firstIn T π = some a} = (T.card : ℝ≥0∞)⁻¹ := by
  classical
  let c := (allOrders V).countP (fun π => decide (firstIn T π = some a))
  have size : T.card*c = (allOrders V).length := by
    have h := total_first V T sub ⟨a,ha⟩
    calc
      _ = ∑ _z ∈ T, c := by simp
      _ = _ := (Finset.sum_congr rfl (fun z hz => equally_often_first V T sub ha hz)).trans h
  have positive : 0 < (allOrders V).length := by simp [allOrders,List.length_permutations,Nat.factorial_pos]
  have cp : c ≠ 0 := by intro zero; simp [zero] at size; omega
  rw [order_mass]
  change ((allOrders V).length:ℝ≥0∞)⁻¹ * (c:ℝ≥0∞) = _
  rw [←size,Nat.cast_mul,ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))]
  rw [mul_assoc,ENNReal.inv_mul_cancel (by exact_mod_cast cp) (by simp),mul_one]

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

lemma radius_window {L : ℝ} (pos : 0 < L) (t δ : ℝ) :
    radiusLaw L (Icc t (t+δ)) ≤ ENNReal.ofReal (16*δ/L) := by
  rw [radiusLaw,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal (L/16))⁻¹ * volume (Icc t (t+δ)) := by gcongr; apply Measure.restrict_le_self
    _ = _ := by
      rw [Real.volume_Icc,add_sub_cancel_left,show 16*δ/L = δ/(L/16) by ring,
        ENNReal.ofReal_div_of_pos (x:=δ) (y:=L/16) (by positivity)]
      exact mul_comm _ _

lemma harmonic_tail (b m : ℕ) (hb : 0 < b) :
    ∑ j ∈ Finset.range m, 1/((b:ℝ)+j+1) ≤ Real.log (1+(m:ℝ)/b) := by
  have b0 : 0 < (b:ℝ) := by exact_mod_cast hb
  have sum (k : ℕ) : ∑ j ∈ Finset.range k, 1/((b:ℝ)+j+1) ≤ Real.log ((b:ℝ)+k)-Real.log b := by
    induction k with
    | zero => simp
    | succ k ih =>
      let t := (b:ℝ)+k
      have t0 : 0 < t := by dsimp [t]; positivity
      have tp : 0 < t+1 := by linarith
      have h := Real.one_sub_inv_le_log_of_pos (div_pos tp t0)
      have eq : 1-((t+1)/t)⁻¹ = 1/(t+1) := by rw [inv_div]; field_simp; ring
      rw [eq,Real.log_div tp.ne' t0.ne'] at h
      rw [Finset.sum_range_succ,Nat.cast_succ]
      change _ ≤ Real.log ((b:ℝ)+(k+1))-Real.log b
      have rew : (b:ℝ)+(k+1) = t+1 := by dsimp [t]; ring
      rw [rew]; change _ + 1/(t+1) ≤ _
      change _ ≤ Real.log t-Real.log b at ih
      linarith
  have arg : (1+(m:ℝ)/b) = ((b:ℝ)+m)/b := by field_simp
  rw [arg,Real.log_div (by positivity) b0.ne']
  exact sum m

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

lemma order_support {n : ℕ} (V : Cluster n) : orderLaw V {π | π ∈ allOrders V} = 1 := by
  rw [order_mass,List.countP_eq_length.mpr (by simp),ENNReal.inv_mul_cancel]
  · simp [allOrders,List.length_permutations,Nat.factorial_ne_zero]
  · simp

/-- Sum the independent order and radius events. Candidate i can be charged
only when it wins among b+i+1 centers and its partial-cover window is hit. -/
theorem ranked_window_bound {n m b : ℕ} (d : Point n → Point n → ℝ) (R L δ : ℝ)
    (pos : 0 < L) (d0 : 0 ≤ δ) (hb : 0 < b) (E : Set (List (Point n) × ℝ))
    (T : Fin m → Cluster n) (z : Fin m → Point n) (t : Fin m → ℝ)
    (sub : ∀ i, T i ⊆ netVertices d R L) (has : ∀ i, z i ∈ T i) (size : ∀ i, (T i).card = b+i.val+1)
    (witness : ∀ p ∈ E, p.1 ∈ allOrders (netVertices d R L) → p.2 ∈ Ico (L/16) (L/8) →
      ∃ i, firstIn (T i) p.1 = some (z i) ∧ p.2 ∈ Icc (t i) (t i+δ)) :
    analysisLaw d R L E ≤ ENNReal.ofReal (16*δ/L * Real.log (1+(m:ℝ)/b)) := by
  classical
  let V := netVertices d R L
  let μ := analysisLaw d R L
  let D : Set (List (Point n) × ℝ) := {π | π ∈ allOrders V} ×ˢ Ico (L/16) (L/8)
  let B := fun i : Fin m => {π | firstIn (T i) π = some (z i)} ×ˢ Icc (t i) (t i+δ)
  letI := order_probability V
  letI := radius_probability pos
  letI : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure ((orderLaw V).prod (radiusLaw L)))
  have full : μ D = 1 := by
    change ((orderLaw V).prod (radiusLaw L)) (_ ×ˢ _) = _
    rw [Measure.prod_prod,order_support,radius_half_open pos,mul_one]
  have measurableD : MeasurableSet D :=
    (show MeasurableSet {π | π ∈ allOrders V} from MeasurableSpace.measurableSet_top).prod measurableSet_Ico
  have no : μ Dᶜ = 0 := by rw [measure_compl measurableD (measure_ne_top _ _),full,measure_univ,tsub_self]
  have covered : E ∩ D ⊆ ⋃ i, B i := by
    rintro p ⟨hp,hd⟩
    obtain ⟨i,hi,hr⟩ := witness p hp hd.1 hd.2
    exact mem_iUnion.mpr ⟨i,hi,hr⟩
  let K := 16*δ/L
  have k0 : 0 ≤ K := by dsimp [K]; positivity
  have term (i : Fin m) : μ (B i) ≤ ENNReal.ofReal (K*(1/((b:ℝ)+i.val+1))) := by
    change ((orderLaw V).prod (radiusLaw L)) (_ ×ˢ _) ≤ _
    rw [Measure.prod_prod,order_first_probability V (T i) (sub i) (z i) (has i),size]
    have h := radius_window pos (t i) δ
    calc
      _ ≤ (((b+i.val+1:ℕ):ℝ≥0∞))⁻¹ * ENNReal.ofReal K := by gcongr
      _ = _ := by
        rw [one_div,ENNReal.ofReal_mul k0,ENNReal.ofReal_inv_of_pos (by positivity),mul_comm]
        have castEq : (b:ℝ)+i.val+1 = ((b+i.val+1:ℕ):ℝ) := by norm_cast
        rw [castEq,ENNReal.ofReal_natCast]
  change μ E ≤ _
  calc
    _ = μ (E ∩ D) := (measure_inter_conull no).symm
    _ ≤ ∑ i, μ (B i) := (measure_mono covered).trans (measure_iUnion_fintype_le μ B)
    _ ≤ ∑ i, ENNReal.ofReal (K*(1/((b:ℝ)+i.val+1))) := Finset.sum_le_sum (fun i _ => term i)
    _ = ENNReal.ofReal (K*∑ j ∈ Finset.range m, 1/((b:ℝ)+j+1)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg k0 (by positivity)),←Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1/((b:ℝ)+j+1))]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (harmonic_tail b m hb) k0)

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical
namespace StableMSR.Recovery.Supplement

noncomputable def carveLabel {n : ℕ} (d : Point n → Point n → ℝ) (N : Cluster n) (π : List (Point n))
    (β : ℝ) (x : Point n) := (firstIn (N.filter (fun z => d z x ≤ β)) π).getD x

lemma initial_wide_label {n : ℕ} (d : Point n → Point n → ℝ) (R L β : ℝ) (π : List (Point n))
    (x : Point n) (U : Cluster n) (eq : component d R Finset.univ x = U) (wide : L < diameter d U) :
    initialLabel d R L β π x = carveLabel d (greedyNet d R U) π β x := by
  simp only [initialLabel,eq,if_pos wide,carveLabel,firstIn,Finset.mem_filter,List.head?_filter]

lemma first_of_subset {n : ℕ} {A B : Cluster n} (sub : A ⊆ B) {π : List (Point n)}
    {z : Point n} (hit : firstIn B π = some z) (hz : z ∈ A) : firstIn A π = some z := by
  obtain ⟨_,as,bs,eq,miss⟩ := List.find?_eq_some_iff_append.mp hit
  apply List.find?_eq_some_iff_append.mpr
  refine ⟨by simpa using hz,as,bs,eq,?_⟩
  intro a ha
  have h : a ∉ B := by simpa using miss a ha
  simpa using (fun hx => h (sub hx) : a ∉ A)

noncomputable def rankedOuter {n : ℕ} (A : Cluster n) (t : Point n → ℝ) : List (Point n) :=
  (A.sort (· ≤ ·)).mergeSort (fun x y => decide (t x ≤ t y))

lemma ranked_outer_spec {n : ℕ} (A : Cluster n) (t : Point n → ℝ) :
    (rankedOuter A t).Nodup ∧ (∀ x, x ∈ rankedOuter A t ↔ x ∈ A) ∧
    (rankedOuter A t).length = A.card ∧ (rankedOuter A t).Pairwise (fun x y => t x ≤ t y) := by
  have perm := List.mergeSort_perm (A.sort (· ≤ ·)) (fun x y => decide (t x ≤ t y))
  refine ⟨perm.nodup_iff.mpr (A.sort_nodup _),fun x => perm.mem_iff.trans (Finset.mem_sort _),?_,?_⟩
  · simp [rankedOuter]
  · exact List.pairwise_mergeSort (le:=fun a b => decide (t a ≤ t b))
      (by simp only [decide_eq_true_eq]; exact fun _ _ _ => le_trans)
      (by intro x y; simp [le_total]) _ |>.imp (fun h => of_decide_eq_true h)

def rankPrefix {n : ℕ} (I : Cluster n) (l : List (Point n)) (i : Fin l.length) : Cluster n :=
  I ∪ (l.take (i.val+1)).toFinset

lemma prefix_spec {n : ℕ} (I V : Cluster n) (l : List (Point n)) (hi : I ⊆ V) (nd : l.Nodup)
    (dis : ∀ v ∈ l, v ∉ I) (sub : ∀ v ∈ l, v ∈ V) (i : Fin l.length) :
    rankPrefix I l i ⊆ V ∧ l.get i ∈ rankPrefix I l i ∧ (rankPrefix I l i).card = I.card+i.val+1 := by
  have disj : Disjoint I (l.take (i.val+1)).toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hI hv; exact dis v (List.mem_of_mem_take (List.mem_toFinset.mp hv)) hI
  refine ⟨Finset.union_subset hi (fun v hv => sub v (List.mem_of_mem_take (List.mem_toFinset.mp hv))),?_,?_⟩
  · apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    exact List.mem_take_iff_getElem.mpr ⟨i.val,lt_min (by omega) i.isLt,rfl⟩
  · rw [rankPrefix,Finset.card_union_of_disjoint disj,List.toFinset_card_of_nodup (nd.sublist (List.take_sublist ..)),
      List.length_take,min_eq_left i.isLt]
    omega

/-- A split on S forces a partial-cover radius window and a first position
among all inner centers and the earlier outer centers. Ties in distances use
the list order, so each rank has a definite denominator. -/
lemma carve_witness {n : ℕ} (d : Point n → Point n → ℝ) (S N I V : Cluster n) (hne : S.Nonempty)
    (ins : I.Nonempty) (iN : I ⊆ N) (nV : N ⊆ V) (L δ : ℝ)
    (inner : ∀ z ∈ I, ∀ x ∈ S, d z x ≤ L/16)
    (span : ∀ z ∈ N, ∀ x ∈ S, ∀ y ∈ S, d z y ≤ d z x + δ)
    (π : List (Point n)) (order : π ∈ allOrders V) (β : ℝ) (lo : L/16 ≤ β) (hi : β ≤ L/8)
    (cut : ∃ x ∈ S, ∃ y ∈ S, carveLabel d N π β x ≠ carveLabel d N π β y) :
    let t := fun z => S.inf' hne (d z)
    let A := (N \ I).filter (fun z => t z ≤ L/8)
    let l := rankedOuter A t
    ∃ i : Fin l.length, firstIn (rankPrefix I l i) π = some (l.get i) ∧
      β ∈ Set.Icc (t (l.get i)) (t (l.get i)+δ) := by
  classical
  let t := fun z => S.inf' hne (d z)
  let A := (N \ I).filter (fun z => t z ≤ L/8)
  let l := rankedOuter A t
  let eligible := N.filter (fun z => t z ≤ β)
  have innerEligible : I ⊆ eligible := by
    intro v hv
    obtain ⟨x,hx⟩ := hne
    exact Finset.mem_filter.mpr ⟨iN hv,((Finset.inf'_le (d v) hx).trans (inner v hv x hx)).trans lo⟩
  obtain ⟨v,hv⟩ := ins
  have vπ : v ∈ π := (List.mem_permutations.mp order).mem_iff.mpr (by simpa using nV (iN hv))
  have existsFirst : (firstIn eligible π).isSome := List.find?_isSome.mpr
    ⟨v,vπ,by simpa using innerEligible hv⟩
  obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp existsFirst
  have zel : z ∈ eligible := of_decide_eq_true (List.find?_some (p:=fun y => decide (y ∈ eligible)) hz)
  obtain ⟨zn,meet⟩ := Finset.mem_filter.mp zel
  have misses : ∃ y ∈ S, β < d z y := by
    by_contra! covers
    have all (x : Point n) (hx : x ∈ S) : carveLabel d N π β x = z := by
      let H := N.filter (fun a => d a x ≤ β)
      have sub : H ⊆ eligible := by
        intro a ha
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,
          (Finset.inf'_le (d a) hx).trans (Finset.mem_filter.mp ha).2⟩
      have eq := first_of_subset sub hz (Finset.mem_filter.mpr ⟨zn,covers x hx⟩)
      change (firstIn H π).getD x = z
      rw [eq]; rfl
    obtain ⟨a,ha,b,hb,h⟩ := cut
    exact h ((all a ha).trans (all b hb).symm)
  obtain ⟨y,hy,late⟩ := misses
  have notIn : z ∉ I := fun h => late.not_ge ((inner z h y hy).trans lo)
  have za : z ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨zn,notIn⟩,meet.trans hi⟩
  obtain ⟨nd,mem,_,sorted⟩ := ranked_outer_spec A t
  obtain ⟨i,zi⟩ := List.mem_iff_get.mp ((mem _).mpr za)
  change l.get i = z at zi
  have pref := prefix_spec I V l (iN.trans nV) nd
    (fun a h => (Finset.mem_sdiff.mp (Finset.mem_filter.mp ((mem a).mp h)).1).2)
    (fun a h => nV (Finset.mem_sdiff.mp (Finset.mem_filter.mp ((mem a).mp h)).1).1) i
  have sub : rankPrefix I l i ⊆ eligible := by
    intro a ha
    rcases Finset.mem_union.mp ha with hI|out
    · exact innerEligible hI
    obtain ⟨j,hj,rfl⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp out)
    have hji := (lt_min_iff.mp hj).1
    have jl := (lt_min_iff.mp hj).2
    have edge : t l[j] ≤ t (l.get i) := by
      rcases lt_or_eq_of_le (show j ≤ i.val by omega) with lt|eq
      · exact sorted.rel_get_of_lt (a:=⟨j,jl⟩) (b:=i) lt
      · subst j; exact le_rfl
    obtain ⟨inside,_⟩ := Finset.mem_filter.mp ((mem _).mp (List.getElem_mem jl))
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp inside).1,edge.trans (zi ▸ meet)⟩
  obtain ⟨x,hx,minEq⟩ := Finset.exists_mem_eq_inf' hne (d z)
  have upper := span z zn x hx y hy
  change t z = d z x at minEq
  dsimp only
  refine ⟨i,?_,?_⟩
  · rw [zi]; exact first_of_subset sub hz (zi ▸ pref.2.1)
  · rw [zi]; exact ⟨meet,by linarith⟩

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical
namespace StableMSR.Recovery.Supplement

/-- The point whose initial label is used in the simultaneous relabelling. -/
noncomputable def labelPoint {n : ℕ} (d : Point n → Point n → ℝ) (b : ℝ) (x : Point n) : Point n :=
  let K := component d (2*b) Finset.univ x
  if radius d K < b then representative K x else x

lemma label_point_distance {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (b : ℝ) (b0 : 0 ≤ b)
    (x : Point n) : d x (labelPoint d b x) ≤ 2*b := by
  classical
  let K := component d (2*b) Finset.univ x
  have hx : x ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.refl x⟩
  have ne : K.Nonempty := ⟨x,hx⟩
  by_cases small : radius d K < b
  · have hm : representative K x ∈ K := by simpa [representative,ne] using K.min'_mem ne
    change d x (if radius d K < b then representative K x else x) ≤ _
    rw [if_pos small]
    linarith [GrowthAux.diameter_bound hd hx hm]
  · change d x (if radius d K < b then representative K x else x) ≤ _
    rw [if_neg small]
    obtain ⟨m,h⟩ := hd
    letI := m
    rw [←h,dist_self]; linarith

lemma reach_of_close {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d) (R : ℝ)
    (x y : Point n) (close : d x y ≤ R) : (thresholdGraph d R Finset.univ).Reachable x y := by
  by_cases eq : x = y
  · subst y; exact .refl _
  · exact (show (thresholdGraph d R Finset.univ).Adj x y from ⟨eq,Finset.mem_univ _,Finset.mem_univ _,
      close,(GrowthAux.metric_symm hd y x) ▸ close⟩).reachable

lemma component_same {n : ℕ} (d : Point n → Point n → ℝ) (R : ℝ) {x y : Point n}
    (walk : (thresholdGraph d R Finset.univ).Reachable x y) :
    component d R Finset.univ y = component d R Finset.univ x := by
  ext v; simp only [component,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨walk.trans,walk.symm.trans⟩

/-- All representatives of a large cluster remain in its original R-component
and lie within 3r of its center. -/
theorem cluster_core {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (C : Cluster n) (c : Point n) (center : OptimalCenter d C c) (R b : ℝ)
    (b0 : 0 ≤ b) (blarge : b ≤ radius d C) (rmax : radius d C ≤ R) (step : 2*b ≤ R) :
    let S := C.image (labelPoint d b)
    S.Nonempty ∧ ∀ y ∈ S, d c y ≤ 3*radius d C ∧
      component d R Finset.univ y = component d R Finset.univ c := by
  refine ⟨⟨_,Finset.mem_image_of_mem _ center.1⟩,?_⟩
  intro y hy
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  have cx := GrowthAux.distance_le_radius center hx
  have xy := label_point_distance d hd b b0 x
  exact ⟨by linarith [GrowthAux.metric_triangle hd c x (labelPoint d b x)],
    component_same d R ((reach_of_close d hd R c x (cx.trans rmax)).trans
      (reach_of_close d hd R x _ (xy.trans step)))⟩

lemma split_labels {n : ℕ} (C : Cluster n) (f : Point n → Point n)
    (cut : Split C ((Finset.univ : Cluster n).image (fun a => Finset.univ.filter (fun x => f x = f a)))) :
    ∃ x ∈ C, ∃ y ∈ C, f x ≠ f y := by
  classical
  by_contra! uniform
  apply cut.not_ge
  apply Finset.card_le_one.mpr
  intro A hA B hB
  obtain ⟨hA,x,hx⟩ := Finset.mem_filter.mp hA
  obtain ⟨hB,y,hy⟩ := Finset.mem_filter.mp hB
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hB
  obtain ⟨hx,hxC⟩ := Finset.mem_inter.mp hx
  obtain ⟨hy,hyC⟩ := Finset.mem_inter.mp hy
  have eq := ((Finset.mem_filter.mp hx).2.symm.trans (uniform x hxC y hyC)).trans (Finset.mem_filter.mp hy).2
  rw [eq]

lemma split_core_labels {n : ℕ} (d : Point n → Point n → ℝ) (ε R L β : ℝ) (C : Cluster n) (π : List (Point n))
    (cut : Split C (partitionAt d ε R L β π)) :
    let S := C.image (labelPoint d (ε*R/4))
    ∃ x ∈ S, ∃ y ∈ S, initialLabel d R L β π x ≠ initialLabel d R L β π y := by
  obtain ⟨x,hx,y,hy,ne⟩ := split_labels C (fun a => initialLabel d R L β π (labelPoint d (ε*R/4) a)) cut
  exact ⟨_,Finset.mem_image_of_mem _ hx,_,Finset.mem_image_of_mem _ hy,ne⟩

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
open MeasureTheory Set
namespace StableMSR.Recovery.Supplement

/-- The split event for one large cluster under the paper's product law and
its actual simultaneous relabelling. -/
theorem one_cluster_split {n k : ℕ} (d : Point n → Point n → ℝ) (γ L : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O) (hL : sigma*largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ-1))
    (C : Cluster n) (hC : C ∈ largeClusters d O (γ-1)) :
    analysisLaw d (largestRadius d O) L {p | Split C (partitionAt d (γ-1) (largestRadius d O) L p.2 p.1)} ≤
      ENNReal.ofReal (chi*radius d C/L * Real.log (1+12*sigma/(γ-1)^2)) := by
  classical
  let ε := γ-1
  let R := largestRadius d O
  let b := ε*R/4
  let r := radius d C
  have r0 : 0 < R := GrowthAux.largest_pos hd hO.1 hkn
  have e0 : 0 < ε := sub_pos.mpr hγ.1
  have e1 : ε < 1 := by dsimp [ε]; linarith [hγ.2]
  have sc : 512*R ≤ L := hL.1
  have pos : 0 < L := by linarith
  have b0 : 0 < b := by dsimp [b]; positivity
  obtain ⟨inc,big⟩ := Finset.mem_filter.mp hC
  change b ≤ r at big
  have rp : 0 < r := b0.trans_le big
  have rmax : r ≤ R := GrowthAux.radius_le_largest inc
  obtain ⟨c,hc⟩ := GrowthAux.exists_center d (hO.1.2.1 C inc)
  let U := component d R Finset.univ c
  let S := C.image (labelPoint d b)
  let E : Set (List (Point n) × ℝ) := {p | Split C (partitionAt d ε R L p.2 p.1)}
  have step : 2*b ≤ R := by dsimp [b]; nlinarith [mul_le_mul_of_nonneg_right e1.le r0.le]
  obtain ⟨hne,core⟩ := cluster_core d hd C c hc R b b0.le big rmax step
  change S.Nonempty at hne
  change ∀ y ∈ S, d c y ≤ 3*r ∧ component d R Finset.univ y = U at core
  change analysisLaw d R L E ≤ ENNReal.ofReal (chi*r/L*Real.log (1+12*sigma/ε^2))
  by_cases wide : L < diameter d U
  · let N := greedyNet d R U
    let V := netVertices d R L
    let I := N ∩ ball d c (L/32)
    let t := fun z : Point n => S.inf' hne (d z)
    let A := (N \ I).filter (fun z => t z ≤ L/8)
    let l := rankedOuter A t
    have wu : U ∈ wideComponents d R L :=
      Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩,wide⟩
    have cu : c ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.refl c⟩
    obtain ⟨low,high⟩ := net_counts d γ L O hk hkn hd hγ hO hL U wu c cu
    change L/(sigma*R) ≤ (I.card:ℝ) at low
    have den : 0 < sigma*R := by dsimp [sigma]; positivity
    have ic : 0 < I.card := by exact_mod_cast (div_pos pos den).trans_le low
    have nV : N ⊆ V := fun z hz => Finset.mem_biUnion.mpr ⟨U,wu,hz⟩
    have iN : I ⊆ N := Finset.inter_subset_left
    have inner (z : Point n) (hz : z ∈ I) (x : Point n) (hx : x ∈ S) : d z x ≤ L/16 := by
      have close := (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2
      have tri := GrowthAux.metric_triangle hd z c x
      rw [GrowthAux.metric_symm hd z c] at tri
      linarith [(core x hx).1]
    have span (z : Point n) (_ : z ∈ N) (x : Point n) (hx : x ∈ S) (y : Point n) (hy : y ∈ S) :
        d z y ≤ d z x+6*r := by
      have a := GrowthAux.metric_triangle hd x c y
      rw [GrowthAux.metric_symm hd x c] at a
      linarith [(core x hx).1,(core y hy).1,GrowthAux.metric_triangle hd z x y]
    obtain ⟨nd,mem,sz,_⟩ := ranked_outer_spec A t
    have pref (i : Fin l.length) := prefix_spec I V l (iN.trans nV) nd
      (fun z hz => (Finset.mem_sdiff.mp (Finset.mem_filter.mp ((mem z).mp hz)).1).2)
      (fun z hz => nV (Finset.mem_sdiff.mp (Finset.mem_filter.mp ((mem z).mp hz)).1).1) i
    have bound := ranked_window_bound d R L (6*r) pos (by positivity) ic E
      (rankPrefix I l) l.get (fun i => t (l.get i)) (fun i => (pref i).1)
      (fun i => (pref i).2.1) (fun i => (pref i).2.2) (by
        intro p hp order range
        obtain ⟨x,hx,y,hy,neq⟩ := split_core_labels d ε R L p.2 C p.1 hp
        rw [initial_wide_label d R L p.2 p.1 x U (core x hx).2 wide,
            initial_wide_label d R L p.2 p.1 y U (core y hy).2 wide] at neq
        exact carve_witness d S N I V hne (Finset.card_pos.mp ic) iN nV L (6*r) inner span
          p.1 order p.2 range.1 range.2.le ⟨x,hx,y,hy,neq⟩)
    have outerSub : A ⊆ N ∩ ball d c (L/4) := by
      intro z hz
      obtain ⟨hN,near⟩ := Finset.mem_filter.mp hz
      obtain ⟨x,hx,eq⟩ := Finset.exists_mem_eq_inf' hne (d z)
      change t z = d z x at eq
      have tri := GrowthAux.metric_triangle hd c x z
      rw [GrowthAux.metric_symm hd x z] at tri
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hN).1,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,by linarith [(core x hx).1]⟩⟩
    have om : (l.length:ℝ) ≤ 12*L/(ε^2*R) := by
      have nat : l.length ≤ (N ∩ ball d c (L/4)).card := sz.le.trans (Finset.card_le_card outerSub)
      exact (show (l.length:ℝ) ≤ _ by exact_mod_cast nat).trans high
    have ratio : (l.length:ℝ)/I.card ≤ 12*sigma/ε^2 := by
      apply (div_le_iff₀ (by exact_mod_cast ic)).mpr
      calc
        _ ≤ _ := om
        _ = (12*sigma/ε^2)*(L/(sigma*R)) := by dsimp [sigma]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left low (by dsimp [sigma]; positivity)
    apply bound.trans
    apply ENNReal.ofReal_le_ofReal
    rw [show 16*(6*r)/L = chi*r/L by unfold chi; ring]
    apply mul_le_mul_of_nonneg_left _ (by unfold chi; positivity)
    exact Real.log_le_log (by positivity) (by linarith)
  · have empty : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨x,hx,y,hy,neq⟩ := split_core_labels d ε R L p.2 C p.1 hp
      apply neq
      simp only [initialLabel,(core x hx).2,(core y hy).2,if_neg wide]
      have ne : U.Nonempty := ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.refl c⟩⟩
      simp [representative,ne]
    rw [empty,measure_empty]; exact bot_le

end StableMSR.Recovery.Supplement
set_option autoImplicit false
open scoped Classical ENNReal
namespace StableMSR.Recovery.Supplement
theorem derived_split_estimates {n k : ℕ} (d : Point n → Point n → ℝ) (γ L : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O)
    (hV : netVertices d (largestRadius d O) L ≠ ∅)
    (hL : sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1)) :
    (∀ C ∈ largeClusters d O (γ - 1),
      (analysisLaw d (largestRadius d O) L)
        {p | Split C (partitionAt d (γ - 1) (largestRadius d O) L p.2 p.1)} ≤
        ENNReal.ofReal (chi * radius d C / L * Real.log (1 + 12 * sigma / (γ - 1) ^ 2))) ∧
    splitExpectation d O (γ - 1) (largestRadius d O) L ≤
      chi * largeMass d O (γ - 1) / L * Real.log (1 + 12 * sigma / (γ - 1) ^ 2) := by
  classical
  let ε := γ-1
  let R := largestRadius d O
  let T := largeClusters d O ε
  let a := Real.log (1+12*sigma/ε^2)
  have e0 : 0 < ε := sub_pos.mpr hγ.1
  have r0 : 0 < R := GrowthAux.largest_pos hd hO.1 hkn
  have l0 : 0 < L := by have h : 512*R ≤ L := hL.1; linarith
  have a0 : 0 ≤ a := Real.log_nonneg (le_add_of_nonneg_right (by dsimp [sigma]; positivity))
  have single := one_cluster_split d γ L O hk hkn hd hγ hO hL
  refine ⟨single,?_⟩
  calc
    splitExpectation d O ε R L ≤ ∑ C ∈ T, chi*radius d C/L*a := by
      apply Finset.sum_le_sum
      intro C hC
      have rad := GrowthAux.radius_nonneg hd (hO.1.2.1 C (Finset.mem_filter.mp hC).1)
      have non : 0 ≤ chi*radius d C/L*a := by dsimp [chi]; positivity
      calc
        _ ≤ (ENNReal.ofReal (chi*radius d C/L*a)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (single C hC)
        _ = _ := ENNReal.toReal_ofReal non
    _ = chi*largeMass d O ε/L*a := by
      simp only [largeMass,cost,T,Finset.sum_mul,Finset.mul_sum,Finset.sum_div]

end StableMSR.Recovery.Supplement
open StableMSR.Recovery.Supplement
theorem solution {n k : ℕ} (d : Point n → Point n → ℝ) (γ L : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O)
    (hV : netVertices d (largestRadius d O) L ≠ ∅)
    (hL : sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1)) :
    (∀ C ∈ largeClusters d O (γ - 1),
      (analysisLaw d (largestRadius d O) L)
        {p | Split C (partitionAt d (γ - 1) (largestRadius d O) L p.2 p.1)} ≤
        ENNReal.ofReal (chi * radius d C / L * Real.log (1 + 12 * sigma / (γ - 1) ^ 2))) ∧
    splitExpectation d O (γ - 1) (largestRadius d O) L ≤
      chi * largeMass d O (γ - 1) / L * Real.log (1 + 12 * sigma / (γ - 1) ^ 2) := by
  exact derived_split_estimates d γ L O hk hkn hd hγ hO hV hL
