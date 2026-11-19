-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.net_counts
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-18T23:59:33.35481+00:00
-- url     : https://prove2.me/submissions/8506aa42-0e7b-40b3-923c-e303637d4d66

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions
import Theorems.Thm_StableMSR_Recovery_local_cluster_density
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery
namespace NetCountSupport
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

lemma diameter_bound {n : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {C : Cluster n} {x y : Point n} (hx : x ∈ C) (hy : y ∈ C) :
    d x y ≤ 2 * radius d C := by
  obtain ⟨c, hc⟩ := exists_center d ⟨x, hx⟩
  have hcx := distance_le_radius hc hx
  have hcy := distance_le_radius hc hy
  have htri := metric_triangle hd x c y
  rw [metric_symm hd x c] at htri
  linarith

lemma separated_card_le_meeting {n k : ℕ} {d : Point n → Point n → ℝ}
    (hd : IsMetricArray d) {O : Partition n} (hO : Feasible Finset.univ k O)
    (B : Cluster n) (x : Point n) (u : ℝ)
    (hsep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → 2 * largestRadius d O < d a b)
    (hball : ∀ y ∈ B, d x y ≤ u) :
    B.card ≤ (meeting O (ball d x u)).card := by
  classical
  have hcover : ∀ y : Point n, ∃ C ∈ O, y ∈ C := by
    intro y
    have hy : y ∈ O.biUnion id := by rw [hO.2.2.2]; simp
    exact Finset.mem_biUnion.mp hy
  choose owner hownerO howner using hcover
  apply Finset.card_le_card_of_injOn owner
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨hownerO y, y, ?_⟩
    exact Finset.mem_inter.mpr ⟨howner y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hball y hy⟩⟩
  · intro a ha b hb hab
    by_contra hne
    have hbC : b ∈ owner a := by rw [hab]; exact howner b
    have hdiam := diameter_bound hd (howner a) hbC
    have hmax := radius_le_largest (d := d) (hownerO a)
    have hstrict := hsep a ha b hb hne
    linarith

lemma meeting_card_split {n : ℕ} (d : Point n → Point n → ℝ)
    (O : Partition n) (ε : ℝ) (A : Cluster n) :
    (meeting O A).card = (meeting (smallClusters d O ε) A).card +
      (meeting (largeClusters d O ε) A).card := by
  classical
  have hunion : meeting O A = meeting (smallClusters d O ε) A ∪
      meeting (largeClusters d O ε) A := by
    ext C
    simp only [meeting, smallClusters, largeClusters, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hCO, hmeet⟩
      rcases lt_or_ge (radius d C) (smallThreshold d O ε) with h | h
      · exact Or.inl ⟨⟨hCO, h⟩, hmeet⟩
      · exact Or.inr ⟨⟨hCO, h⟩, hmeet⟩
    · rintro (⟨⟨hCO, _⟩, hmeet⟩ | ⟨⟨hCO, _⟩, hmeet⟩) <;> exact ⟨hCO, hmeet⟩
  have hdis : Disjoint (meeting (smallClusters d O ε) A) (meeting (largeClusters d O ε) A) := by
    apply Finset.disjoint_left.mpr
    intro C hCS hCL
    have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp hCS).1).2
    have hl := (Finset.mem_filter.mp (Finset.mem_filter.mp hCL).1).2
    exact not_lt_of_ge hl hs
  rw [hunion, Finset.card_union_of_disjoint hdis]

end NetCountSupport
namespace StableMSR.Recovery.Supplement
theorem fold_net_properties {n : ℕ} (d : Point n → Point n → ℝ) (sym : ∀ x y, d x y = d y x) (R : ℝ)
    (W : Cluster n) (xs : List (Point n)) (contained : ∀ x ∈ xs, x ∈ W) (A : Cluster n)
    (sub : A ⊆ W) (sep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 2*R < d x y) :
    let B := xs.foldl (fun S x => if ∀ z ∈ S, 2*R < d x z then insert x S else S) A
    B ⊆ W ∧ ∀ x ∈ B, ∀ y ∈ B, x ≠ y → 2*R < d x y := by
  classical
  induction xs generalizing A with
  | nil => exact ⟨sub,sep⟩
  | cons x xs ih =>
    have tail : ∀ y ∈ xs, y ∈ W := fun y hy => contained y (by simp [hy])
    simp only [List.foldl_cons]
    by_cases far : ∀ z ∈ A, 2*R < d x z
    · rw [if_pos far]
      apply ih tail
      · exact Finset.insert_subset (contained x List.mem_cons_self) sub
      · intro a ha b hb ab
        rcases Finset.mem_insert.mp ha with hax|haA
        · rcases Finset.mem_insert.mp hb with hbx|hbB
          · exact (ab (hax.trans hbx.symm)).elim
          · simpa only [hax] using far _ hbB
        · rcases Finset.mem_insert.mp hb with hbx|hbB
          · rw [hbx,sym a x]; exact far _ haA
          · exact sep _ haA _ hbB ab
    · rw [if_neg far]; exact ih tail A sub sep

theorem prescribed_net_properties {n : ℕ} (d : Point n → Point n → ℝ) (sym : ∀ x y, d x y = d y x)
    (R : ℝ) (W : Cluster n) : greedyNet d R W ⊆ W ∧
    ∀ x ∈ greedyNet d R W, ∀ y ∈ greedyNet d R W, x ≠ y → 2*R < d x y := by
  exact fold_net_properties d sym R W (W.sort (· ≤ ·)) (by simp) ∅ (Finset.empty_subset _) (by simp)

/-- The greedy fold retains its seed points and covers all the scanned points. -/
lemma fold_net_cover {n : ℕ} (d : Point n → Point n → ℝ) (diag : ∀ x, d x x = 0)
    (R : ℝ) (hR : 0 ≤ R) (xs : List (Point n)) (A : Cluster n) :
    let B := xs.foldl (fun S x => if ∀ z ∈ S, 2*R < d x z then insert x S else S) A
    A ⊆ B ∧ ∀ x ∈ xs, ∃ z ∈ B, d x z ≤ 2*R := by
  classical
  induction xs generalizing A with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons]
    by_cases far : ∀ z ∈ A, 2*R < d a z
    · rw [if_pos far]
      obtain ⟨sub,cov⟩ := ih (insert a A)
      refine ⟨(Finset.subset_insert _ _).trans sub,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · exact ⟨x,sub (Finset.mem_insert_self ..),by rw [diag]; linarith⟩
      · exact cov x hx
    · rw [if_neg far]
      obtain ⟨sub,cov⟩ := ih A
      refine ⟨sub,?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · push_neg at far
        obtain ⟨z,hz,hnear⟩ := far
        exact ⟨z,sub hz,hnear⟩
      · exact cov x hx

lemma prescribed_net_cover {n : ℕ} {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {R : ℝ} (hR : 0 ≤ R) (U : Cluster n) {v : Point n} (hv : v ∈ U) :
    ∃ z ∈ greedyNet d R U, d v z ≤ 2*R := by
  have diag (x : Point n) : d x x = 0 := by
    obtain ⟨m,hm⟩ := hd
    letI := m
    rw [←hm,dist_self]
  exact (fold_net_cover d diag R hR (U.sort (· ≤ ·)) ∅).2 v (by simpa using hv)

/-- A walk crossing radial level s contains a point within one edge of that level. -/
lemma radial_crossing {n : ℕ} {d : Point n → Point n → ℝ} (hd : IsMetricArray d)
    {R s : ℝ} (hR : 0 ≤ R) (W : Cluster n) (root x : Point n) {a b : Point n}
    (p : (thresholdGraph d R W).Walk a b) (start : (thresholdGraph d R W).Reachable root a)
    (low : d x a ≤ s) (high : s ≤ d x b) :
    ∃ v, (thresholdGraph d R W).Reachable root v ∧ s ≤ d x v ∧ d x v ≤ s+R := by
  induction p with
  | nil => exact ⟨_,start,high,by linarith⟩
  | @cons a b c edge _ ih =>
    have reach := start.trans edge.reachable
    by_cases h : s ≤ d x b
    · have near : d a b ≤ R := edge.2.2.2.1
      exact ⟨b,reach,h,by linarith [NetCountSupport.metric_triangle hd x a b]⟩
    · exact ih reach (le_of_not_ge h) high

lemma wide_far {n : ℕ} {d : Point n → Point n → ℝ} (hd : IsMetricArray d) (U : Cluster n)
    {L : ℝ} (wide : L < diameter d U) (x : Point n) (hx : x ∈ U) :
    ∃ y ∈ U, L/2 < d x y := by
  classical
  by_contra! small
  have ne : U.Nonempty := ⟨x,hx⟩
  have bound : diameter d U ≤ L := by
    rw [diameter,dif_pos ne]
    apply Finset.sup'_le
    intro a ha
    rw [eccentricity,dif_pos ne]
    apply Finset.sup'_le
    intro b hb
    have tri := NetCountSupport.metric_triangle hd a x b
    rw [NetCountSupport.metric_symm hd a x] at tri
    linarith [small a ha,small b hb]
  exact wide.not_ge bound



/-- Count disjoint radial intervals along one path in a wide component. This
part of the net-count lemma uses only metric connectivity and net coverage. -/
theorem inner_net_count {n : ℕ} (d : Point n → Point n → ℝ) (hd : IsMetricArray d)
    (R L : ℝ) (hR : 0 < R) (hL : sigma*R ≤ L) (U : Cluster n)
    (hU : U ∈ wideComponents d R L) (x : Point n) (hx : x ∈ U) :
    L/(sigma*R) ≤ ((greedyNet d R U ∩ ball d x (L/32)).card : ℝ) := by
  classical
  obtain ⟨hc,wide⟩ := Finset.mem_filter.mp hU
  obtain ⟨root,_,hu⟩ := Finset.mem_image.mp hc
  change component d R Finset.univ root = U at hu
  let G := thresholdGraph d R (Finset.univ : Cluster n)
  have reach (v : Point n) : v ∈ U ↔ G.Reachable root v := by
    rw [←hu]; simp [component,G]
  obtain ⟨y,hy,far⟩ := wide_far hd U wide x hx
  obtain ⟨path⟩ := ((reach x).mp hx).symm.trans ((reach y).mp hy)
  let t := L/(512*R)
  have scale : 512*R ≤ L := hL
  have t0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
  have scaleEq : t*(512*R) = L := div_mul_cancel₀ _ (by positivity)
  let m := ⌊t⌋₊+1
  have floorBound (i : Fin m) : (i.val:ℝ) ≤ t := by
    have hi : i.val ≤ ⌊t⌋₊ := Nat.le_of_lt_succ i.isLt
    exact (show (i.val:ℝ) ≤ (⌊t⌋₊:ℝ) by exact_mod_cast hi).trans (Nat.floor_le t0)
  let N := greedyNet d R U ∩ ball d x (L/32)
  have pick (i : Fin m) : ∃ z ∈ N, 6*R*(i.val:ℝ)-2*R ≤ d x z ∧ d x z ≤ 6*R*(i.val:ℝ)+3*R := by
    have si := mul_le_mul_of_nonneg_right (floorBound i) hR.le
    have limit : 6*R*(i.val:ℝ)+3*R ≤ L/32 := by nlinarith
    have zero : d x x = 0 := by
      obtain ⟨metric,hm⟩ := hd
      letI := metric
      rw [←hm,dist_self]
    obtain ⟨v,rv,lo,hi⟩ := radial_crossing hd hR.le Finset.univ root x path ((reach x).mp hx)
      (s:=6*R*(i.val:ℝ)) (by rw [zero]; positivity) (by have := i.isLt; linarith)
    obtain ⟨z,hz,near⟩ := prescribed_net_cover hd hR.le U ((reach v).mpr rv)
    have tr := NetCountSupport.metric_triangle hd x v z
    have tr' := NetCountSupport.metric_triangle hd x z v
    rw [NetCountSupport.metric_symm hd z v] at tr'
    have upper : d x z ≤ 6*R*(i.val:ℝ)+3*R := by linarith
    exact ⟨z,Finset.mem_inter.mpr ⟨hz,Finset.mem_filter.mpr ⟨Finset.mem_univ _,upper.trans limit⟩⟩,
      by linarith,upper⟩
  choose z hmem lower upper using pick
  have apart (i j : Fin m) (h : i < j) : z i ≠ z j := by
    intro eq
    have gap : (i.val:ℝ)+1 ≤ (j.val:ℝ) := by exact_mod_cast (show i.val+1 ≤ j.val from h)
    have sep := mul_le_mul_of_nonneg_left gap hR.le
    have hi := upper i
    have hj := lower j
    rw [←eq] at hj
    nlinarith
  have injection : Function.Injective (fun i : Fin m => (⟨z i,hmem i⟩ : ↥N)) := by
    intro i j h
    have eq := congrArg Subtype.val h
    rcases lt_trichotomy i j with lt|eq'|gt
    · exact False.elim (apart i j lt eq)
    · exact eq'
    · exact False.elim (apart j i gt eq.symm)
  have card : m ≤ N.card := by simpa using Fintype.card_le_of_injective _ injection
  have tm : t ≤ (m:ℝ) := by simpa only [m,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one t).le
  exact tm.trans (by exact_mod_cast card)



lemma outer_arithmetic (ε R L : ℝ) (e0 : 0 < ε) (e1 : ε < 1) (r0 : 0 < R) (scale : 512*R ≤ L) :
    1 + (2*(L/4)+2*(ε*R/4))/(ε*(ε*R/4)) + (L/4+2*R)/(ε*R/4) ≤ 12*L/(ε^2*R) := by
  have den : 0 < ε^2*R := by positivity
  have eq : (1 + (2*(L/4)+2*(ε*R/4))/(ε*(ε*R/4)) + (L/4+2*R)/(ε*R/4)) * (ε^2*R) =
      ε^2*R+2*L+10*ε*R+ε*L := by field_simp; ring
  have er : ε*R ≤ R := by nlinarith [mul_le_mul_of_nonneg_right e1.le r0.le]
  have esq : ε^2 ≤ 1 := by nlinarith [mul_nonneg e0.le (sub_nonneg.mpr e1.le)]
  have esr := mul_le_mul_of_nonneg_right esq r0.le
  have el := mul_le_mul_of_nonneg_right e1.le (show 0 ≤ L by linarith)
  apply (le_div_iff₀ den).mpr
  rw [eq]; linarith

theorem outer_net_count {n k : ℕ} (d : Point n → Point n → ℝ) (γ L : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O) (hL : sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1))
    (U : Cluster n) (x : Point n) :
    ((greedyNet d (largestRadius d O) U ∩ ball d x (L/4)).card : ℝ) ≤
      12*L/((γ-1)^2*largestRadius d O) := by
  let R := largestRadius d O
  let ε := γ-1
  let u := L/4
  let B := greedyNet d R U ∩ ball d x u
  have r0 : 0 < R := NetCountSupport.largest_pos hd hO.1 hkn
  have scale : 512*R ≤ L := hL.1
  have e0 : 0 < ε := sub_pos.mpr hγ.1
  have e1 : ε < 1 := by dsimp [ε]; linarith [hγ.2]
  have sep := (prescribed_net_properties d (NetCountSupport.metric_symm hd) R U).2
  have hc := NetCountSupport.separated_card_le_meeting hd hO.1 B x u
    (fun a ha b hb hne => sep a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1 hne)
    (fun y hy => (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2)
  rw [NetCountSupport.meeting_card_split d O ε] at hc
  have count : (B.card:ℝ) ≤ ((meeting (smallClusters d O ε) (ball d x u)).card:ℝ) +
      ((meeting (largeClusters d O ε) (ball d x u)).card:ℝ) := by exact_mod_cast hc
  obtain ⟨_,hs,hl⟩ := local_cluster_density d hd k ⟨hk,hkn.le⟩ γ hγ hkn O hO
  have u0 : 0 ≤ u := by dsimp [u]; linarith
  specialize hs x u u0 (by dsimp [u]; linarith [hL.2])
  specialize hl x u u0
  exact (count.trans (add_le_add hs hl)).trans (outer_arithmetic ε R L e0 e1 r0 scale)

end StableMSR.Recovery.Supplement
open StableMSR.Recovery.Supplement
theorem solution {n k : ℕ} (d : Point n → Point n → ℝ) (γ L : ℝ) (O : Partition n)
    (hk : 1 ≤ k) (hkn : k < n) (hd : IsMetricArray d) (hγ : 1 < γ ∧ γ < 2)
    (hO : Stable d k γ O)
    (hL : sigma * largestRadius d O ≤ L ∧ L ≤ densityScale d O (γ - 1))
    (U : Cluster n) (hU : U ∈ wideComponents d (largestRadius d O) L)
    (x : Point n) (hx : x ∈ U) :
    L / (sigma * largestRadius d O) ≤
      ((greedyNet d (largestRadius d O) U ∩ ball d x (L / 32)).card : ℝ) ∧
    ((greedyNet d (largestRadius d O) U ∩ ball d x (L / 4)).card : ℝ) ≤
      12 * L / ((γ - 1) ^ 2 * largestRadius d O) := by
  have r0 := NetCountSupport.largest_pos hd hO.1 hkn
  exact ⟨inner_net_count d hd _ L r0 hL.1 U hU x hx,outer_net_count d γ L O hk hkn hd hγ hO hL U x⟩
