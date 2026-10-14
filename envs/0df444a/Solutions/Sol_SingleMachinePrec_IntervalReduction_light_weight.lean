-- Prove2me | solution 1 for SingleMachinePrec.IntervalReduction.light_weight
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:27:54.492335+00:00
-- url     : https://prove2.me/submissions/2de2481b-b7de-452b-b914-6895c890018d

import Mathlib
import Definitions.Def_SingleMachinePrec_IntervalReduction_Instance



namespace SingleMachinePrec.IntervalReduction

variable {N : ℕ} {G : SimpleGraph (Fin N)}

lemma ceil_nat_cast_sub_half (n : ℕ) (hn : 1 ≤ n) : ⌈((n : ℝ) - 1 / 2)⌉ = (n : ℤ) := by
  rw [Int.ceil_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith

lemma ceil_right (L : TreeLayout G) (x : Job L) :
    ⌈right L x⌉ = match x with
      | .s0 => 0
      | .s j => (num j : ℤ)
      | .m i => ((N + num i : ℕ) : ℤ)
      | .e i => ((N + num i + 1 : ℕ) : ℤ)
      | .b q => (num q.1.2 : ℤ) := by
  cases x with
  | s0 => simp [right]
  | s j => simp only [right]; exact Int.ceil_natCast _
  | m i =>
    simp only [right]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i)]; push_cast; rfl
  | e i =>
    simp only [right]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i + 1)]; push_cast; rfl
  | b q =>
    simp only [right]
    exact ceil_nat_cast_sub_half _ (by simp [num])

lemma ceil_left (L : TreeLayout G) (x : Job L) :
    ⌈left L x⌉ = match x with
      | .s0 => -1
      | .s j => (parNum L j : ℤ)
      | .m i => (num i : ℤ)
      | .e i => ((N + num i : ℕ) : ℤ)
      | .b q => (num q.1.1 : ℤ) := by
  cases x with
  | s0 => simp only [left]; exact Int.ceil_eq_iff.mpr (by norm_num)
  | s j => simp only [left]; exact Int.ceil_natCast _
  | m i =>
    simp only [left]
    exact ceil_nat_cast_sub_half _ (by simp [num])
  | e i =>
    simp only [left]
    rw [← Int.ceil_natCast (R := ℝ) (N + num i)]; push_cast; rfl
  | b q => simp only [left]; exact Int.ceil_natCast _

lemma procTime_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    procTime L k x = 0 ∨ procTime L k x = k ^ (-⌈right L x⌉) := by
  have hk0 : k ≠ 0 := by positivity
  rw [ceil_right]
  cases x with
  | s0 => right; simp [procTime]
  | s j => right; simp [procTime, zpow_neg]
  | m i => right; simp only [procTime]; rw [one_div, ← zpow_natCast, ← zpow_neg]
  | e i => left; simp [procTime]
  | b q => right; simp [procTime, zpow_neg]

lemma weight_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    weight L k x = 0 ∨ weight L k x = k ^ ⌈left L x⌉ := by
  have hk0 : k ≠ 0 := by positivity
  rw [ceil_left]
  cases x with
  | s0 => left; simp [weight]
  | s j => right; simp [weight]
  | m i => right; simp [weight]
  | e i => right; simp only [weight]; exact (zpow_natCast _ _).symm
  | b q => right; simp [weight]

lemma procTime_le (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    procTime L k x ≤ 1 / k ^ ⌈right L x⌉ := by
  have hk0 : 0 < k := by positivity
  rcases procTime_cases L k hk x with h | h
  · rw [h]; positivity
  · rw [h, zpow_neg, one_div]

lemma weight_le (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x : Job L) :
    weight L k x ≤ k ^ ⌈left L x⌉ := by
  have hk0 : 0 < k := by positivity
  rcases weight_cases L k hk x with h | h
  · rw [h]; positivity
  · rw [h]

lemma prod_cases (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L) :
    procTime L k x * weight L k y = 0 ∨
      procTime L k x * weight L k y = k ^ (⌈left L y⌉ - ⌈right L x⌉) := by
  have hk0 : k ≠ 0 := by positivity
  rcases procTime_cases L k hk x with h | h
  · left; rw [h]; simp
  rcases weight_cases L k hk y with h' | h'
  · left; rw [h']; simp
  · right; rw [h, h', ← zpow_add₀ hk0]; congr 1; ring

lemma prod_le_one_of (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : left L y ≤ right L x) :
    procTime L k x * weight L k y ≤ 1 := by
  have hle : ⌈left L y⌉ ≤ ⌈right L x⌉ := Int.ceil_le_ceil h
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0]; norm_num
  · rw [h0]; exact zpow_le_one_of_nonpos₀ hk.le (by omega)

lemma prod_le_inv_of (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : left L y ≤ right L x) (h' : ⌈left L y⌉ ≠ ⌈right L x⌉) :
    procTime L k x * weight L k y ≤ 1 / k := by
  have hk0 : 0 < k := by positivity
  have hle : ⌈left L y⌉ ≤ ⌈right L x⌉ := Int.ceil_le_ceil h
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0]; positivity
  · rw [h0, one_div, ← zpow_neg_one]
    exact zpow_le_zpow_right₀ hk.le (by omega)

lemma prod_eq_one_iff (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (h : procTime L k x * weight L k y = 1) : ⌈left L y⌉ = ⌈right L x⌉ := by
  rcases prod_cases L k hk x y with h0 | h0
  · rw [h0] at h; norm_num at h
  · rw [h0] at h
    have := (zpow_eq_one_iff_right₀ (by linarith) hk.ne').mp h
    omega


lemma parNum_eq_zero (L : TreeLayout G) (j : Fin N) : parNum L j = 0 ↔ L.par j = none := by
  unfold parNum
  cases h : L.par j <;> simp

lemma parNum_eq_num (L : TreeLayout G) (j i : Fin N) : parNum L j = num i ↔ L.par j = some i := by
  unfold parNum num
  cases h : L.par j with
  | none => simp
  | some i' => simp [Fin.ext_iff]

lemma parNum_lt (L : TreeLayout G) (j : Fin N) : parNum L j < N := by
  unfold parNum
  cases h : L.par j with
  | none => simp; exact lt_of_le_of_lt (Nat.zero_le _) j.2
  | some i' =>
    have := L.par_lt j i' h
    have h2 : i'.val < j.val := this
    have := j.2
    simp; omega

lemma num_le (i : Fin N) : num i ≤ N := by unfold num; have := i.2; omega
lemma num_pos (i : Fin N) : 1 ≤ num i := by unfold num; omega
lemma num_inj {i j : Fin N} : num i = num j ↔ i = j := by
  unfold num; simp [Fin.ext_iff]

lemma InD_key (L : TreeLayout G) (x y : Job L) (hinc : Incomparable (prec L) x y)
    (hceil : ⌈left L y⌉ = ⌈right L x⌉) (hx : ∀ i, x ≠ .e i) (hy : y ≠ .s0) : InD L x y := by
  rw [ceil_left, ceil_right] at hceil
  cases x with
  | s0 =>
    cases y with
    | s0 => exact absurd rfl hy
    | s j => simp only [InD]; simp at hceil; exact (parNum_eq_zero L j).mp (by omega)
    | m i => simp at hceil; have := num_pos i; omega
    | e i => simp at hceil; have := num_pos i; omega
    | b q => simp at hceil; have := num_pos q.1.1; omega
  | s j =>
    have h1 := num_le j
    cases y with
    | s0 => exact absurd rfl hy
    | s j' => simp only [InD]; simp at hceil; exact (parNum_eq_num L j' j).mp (by omega)
    | m i => simp at hceil; simp only [InD]; exact (num_inj.mp (by omega)).symm
    | e i => simp at hceil; have := num_pos i; omega
    | b q => simp at hceil; simp only [InD]; exact num_inj.mp (by omega)
  | m i =>
    have h1 := num_le i
    cases y with
    | s0 => exact absurd rfl hy
    | s j' => simp at hceil; have := parNum_lt L j'; omega
    | m i' => simp at hceil; have := num_le i'; have := num_pos i; omega
    | e i' => simp at hceil; simp only [InD]; exact (num_inj.mp (by omega))
    | b q => simp at hceil; have := num_le q.1.1; have := num_pos i; omega
  | e i => exact absurd rfl (hx i)
  | b q =>
    have h1 := num_le q.1.2
    have h2 : (1:ℕ) ≤ num q.1.2 := num_pos _
    cases y with
    | s0 => exact absurd rfl hy
    | s j' =>
      simp at hceil
      exfalso; apply hinc.1; right
      simp only [right, left]
      have : (parNum L j' : ℝ) = num q.1.2 := by exact_mod_cast hceil
      rw [this]; linarith
    | m i' => simp at hceil; simp only [InD]; exact num_inj.mp (by omega)
    | e i' => simp at hceil; have := num_pos i'; omega
    | b q' =>
      simp at hceil
      exfalso; apply hinc.1; right
      simp only [right, left]
      have : (num q'.1.1 : ℝ) = num q.1.2 := by exact_mod_cast hceil
      rw [this]; linarith

lemma claim2_core (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L)
    (hxy : Incomparable (prec L) x y) :
    (InD L x y → procTime L k x * weight L k y = 1) ∧
    (¬ InD L x y → procTime L k x * weight L k y ≤ 1 / k) := by
  have hk0 : k ≠ 0 := by positivity
  constructor
  · intro h
    cases x <;> cases y <;> simp only [InD] at h <;> try contradiction
    · simp [procTime, weight, (parNum_eq_zero L _).mpr h]
    · have := (parNum_eq_num L _ _).mpr h
      simp only [procTime, weight, this]
      field_simp
    all_goals (subst h; simp only [procTime, weight]; field_simp)
  · intro h
    by_cases hx : ∃ i, x = .e i
    · obtain ⟨i, rfl⟩ := hx
      simp [procTime]; positivity
    by_cases hy : y = .s0
    · subst hy; simp [weight]; positivity
    push_neg at hx
    have hle : left L y ≤ right L x := not_lt.mp (fun h => hxy.1 (Or.inr h))
    refine prod_le_inv_of L k hk x y hle ?_
    intro he
    exact h (InD_key L x y hxy he hx hy)

lemma kVal_gt (L : TreeLayout G) : 1 < kVal L := by
  unfold kVal numJobs
  have : 0 < Fintype.card (Job L) := Fintype.card_pos_iff.mpr ⟨Job.s0⟩
  have : (1 : ℝ) ≤ (Fintype.card (Job L) : ℝ) := by exact_mod_cast this
  nlinarith

lemma vw_nonneg (L : TreeLayout G) (k : ℝ) (hk : 1 < k) (x y : Job L) :
    0 ≤ procTime L k x * weight L k y := by
  have hk0 : 0 < k := by positivity
  rcases prod_cases L k hk x y with h | h
  · rw [h]
  · rw [h]; positivity

lemma vc_exists {V : Type*} [Finite V] (H : SimpleGraph V) :
    ∃ D : Finset V, H.IsVertexCover (D : Set V) ∧ (D.card : ℕ∞) = H.vertexCoverNum := by
  obtain ⟨s, hs1, hs2⟩ := SimpleGraph.vertexCoverNum_exists H
  refine ⟨(Set.toFinite s).toFinset, by simpa using hs2, ?_⟩
  rw [← hs1, ← Set.encard_coe_eq_coe_finsetCard]; simp

lemma vc_le_card {V : Type*} (H : SimpleGraph V) (D : Finset V) (hD : H.IsVertexCover (D : Set V)) :
    H.vertexCoverNum ≤ (D.card : ℕ∞) := by
  have := hD.vertexCoverNum_le
  rwa [Set.encard_coe_eq_coe_finsetCard] at this

open Classical in
lemma light_core (L : TreeLayout G) :
    (∑ u : IncPair (prec L),
        if InD L u.1.1 u.1.2 then 0
        else vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u) < 1 := by
  have hk := kVal_gt L
  have hk0 : 0 < kVal L := by linarith
  set n := numJobs L with hn
  have hcard : Fintype.card (IncPair (prec L)) ≤ n * n := by
    calc Fintype.card (IncPair (prec L)) ≤ Fintype.card (Job L × Job L) := Fintype.card_subtype_le _
      _ = n * n := by simp [hn, numJobs]
  have hterm : ∀ u : IncPair (prec L),
      (if InD L u.1.1 u.1.2 then 0
        else vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u) ≤ 1 / kVal L := by
    intro u
    split_ifs with h
    · positivity
    · exact (claim2_core L (kVal L) hk u.1.1 u.1.2 u.2).2 h
  calc _ ≤ ∑ _u : IncPair (prec L), 1 / kVal L := Finset.sum_le_sum (fun u _ => hterm u)
    _ = (Fintype.card (IncPair (prec L)) : ℝ) * (1 / kVal L) := by simp
    _ ≤ ((n * n : ℕ) : ℝ) * (1 / kVal L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ < 1 := by
        have : kVal L = (n : ℝ) ^ 2 + 1 := rfl
        rw [mul_one_div, div_lt_one hk0, this]; push_cast; nlinarith

open Classical in
lemma hone_lem (L : TreeLayout G) (u : IncPair (prec L)) (h : InD L u.1.1 u.1.2) :
    vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u = 1 :=
  (claim2_core L (kVal L) (kVal_gt L) u.1.1 u.1.2 u.2).1 h

open Classical in
lemma lw_up (L : TreeLayout G) (D0 : Finset {u : IncPair (prec L) | InD L u.1.1 u.1.2})
    (hD0 : (GIprime L).IsVertexCover (D0 : Set _)) : tauW L < D0.card + 1 := by
  have hk := kVal_gt L
  have hcov : (vertexCoverGraph (prec L)).IsVertexCover
      ((D0.image Subtype.val ∪ Finset.univ.filter (fun u : IncPair (prec L) => ¬ InD L u.1.1 u.1.2) :
        Finset (IncPair (prec L))) : Set _) := by
    intro u v huv
    by_cases hu : InD L u.1.1 u.1.2
    · by_cases hv : InD L v.1.1 v.1.2
      · have hadj : (GIprime L).Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
          simpa [GIprime, GSI] using huv
        rcases hD0 hadj with h | h
        · left; simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
            Finset.mem_coe]
          exact Or.inl ⟨_, by simpa using h, rfl⟩
        · right; simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
            Finset.mem_coe]
          exact Or.inl ⟨_, by simpa using h, rfl⟩
      · right; simp [hv]
    · left; simp [hu]
  have hdisj : Disjoint (D0.image Subtype.val)
      (Finset.univ.filter (fun u : IncPair (prec L) => ¬ InD L u.1.1 u.1.2)) := by
    rw [Finset.disjoint_left]
    intro u hu hu2
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hu2).2 x.2
  have hw : ∑ u ∈ (D0.image Subtype.val ∪ Finset.univ.filter (fun u : IncPair (prec L) => ¬ InD L u.1.1 u.1.2)),
      vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u =
      (D0.card : ℝ) + ∑ u : IncPair (prec L),
        (if InD L u.1.1 u.1.2 then 0
        else vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u) := by
    rw [Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => Subtype.val_injective h)]
    congr 1
    · rw [Finset.sum_congr rfl (fun x _ => hone_lem L x.1 x.2)]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    · rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro u _; split_ifs <;> simp_all
  have hle : tauW L ≤ ∑ u ∈ (D0.image Subtype.val ∪ Finset.univ.filter (fun u : IncPair (prec L) => ¬ InD L u.1.1 u.1.2)),
      vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u := by
    unfold tauW minWeightVC
    apply Finset.inf'_le
    simpa using hcov
  have := light_core L
  linarith

open Classical in
lemma lw_low (L : TreeLayout G) (m : ℕ)
    (hm : ∀ D : Finset {u : IncPair (prec L) | InD L u.1.1 u.1.2},
      (GIprime L).IsVertexCover (D : Set _) → m ≤ D.card) : (m : ℝ) ≤ tauW L := by
  have hk := kVal_gt L
  obtain ⟨C, hC, hCeq⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ.filter
    (fun C : Finset (IncPair (prec L)) => (vertexCoverGraph (prec L)).IsVertexCover (C : Set _)))
    ⟨Finset.univ, by simp [SimpleGraph.isVertexCover_univ]⟩
    (fun C => ∑ u ∈ C, vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u)
  have hCc : (vertexCoverGraph (prec L)).IsVertexCover (C : Set _) := by simpa using hC
  have htau : tauW L = ∑ u ∈ C, vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u :=
    hCeq
  have hcov' : (GIprime L).IsVertexCover
      ((Finset.univ.filter (fun x : {u : IncPair (prec L) | InD L u.1.1 u.1.2} => x.1 ∈ C) :
        Finset _) : Set _) := by
    intro x y hxy
    have hadj : (vertexCoverGraph (prec L)).Adj x.1 y.1 := by simpa [GIprime, GSI] using hxy
    rcases hCc hadj with h | h
    · left; exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · right; exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have h2 := hm _ hcov'
  have h3 : ((Finset.univ.filter (fun x : {u : IncPair (prec L) | InD L u.1.1 u.1.2} => x.1 ∈ C)).card : ℝ)
      ≤ ∑ u ∈ C, vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u := by
    have : ∑ u ∈ (Finset.univ.filter (fun x : {u : IncPair (prec L) | InD L u.1.1 u.1.2} => x.1 ∈ C)).image Subtype.val,
        vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u
        = (Finset.univ.filter (fun x : {u : IncPair (prec L) | InD L u.1.1 u.1.2} => x.1 ∈ C)).card := by
      rw [Finset.sum_image (fun a _ b _ h => Subtype.val_injective h)]
      rw [Finset.sum_congr rfl (fun x _ => hone_lem L x.1 x.2)]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← this]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hx).2
    · intro u _ _; exact vw_nonneg L _ hk _ _
  rw [htau]
  exact le_trans (by exact_mod_cast h2) h3

open Classical in
theorem lw_core (L : TreeLayout G) :
    (∑ u : IncPair (prec L),
        if InD L u.1.1 u.1.2 then 0
        else vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u) < 1 ∧
    (GIprime L).vertexCoverNum = ((⌊tauW L⌋₊ : ℕ) : ℕ∞) := by
  refine ⟨light_core L, ?_⟩
  obtain ⟨D0, hD0, hD0c⟩ := vc_exists (GIprime L)
  have hfin : (GIprime L).vertexCoverNum ≠ ⊤ := SimpleGraph.vertexCoverNum_ne_top_of_finite
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  have hD0m : D0.card = m := by rw [← hm] at hD0c; exact_mod_cast hD0c
  have hup := lw_up L D0 hD0
  rw [hD0m] at hup
  have hlow := lw_low L m (fun D hD => by
    have h1 := vc_le_card _ D hD
    rw [← hm] at h1
    exact_mod_cast h1)
  rw [← hm]
  have : ⌊tauW L⌋₊ = m := by
    rw [Nat.floor_eq_iff (by have := Nat.cast_nonneg (α := ℝ) m; linarith)]
    exact ⟨hlow, hup⟩
  rw [this]

end SingleMachinePrec.IntervalReduction

open SingleMachinePrec.IntervalReduction
open Classical

theorem solution {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    (∑ u : IncPair (prec L),
        if InD L u.1.1 u.1.2 then 0
        else vertexWeight (prec L) (procTime L (kVal L)) (weight L (kVal L)) u) < 1 ∧
    (GIprime L).vertexCoverNum = ((⌊tauW L⌋₊ : ℕ) : ℕ∞) := by
  exact lw_core L
