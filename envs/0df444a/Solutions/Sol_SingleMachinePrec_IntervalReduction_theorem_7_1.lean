-- Prove2me | solution 1 for SingleMachinePrec.IntervalReduction.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:41:22.260748+00:00
-- url     : https://prove2.me/submissions/b0a89360-1d89-4547-8ccd-ead7a19e6d14

import Mathlib
import Definitions.Def_AppliedComb_Posets_intervalOrder
import Definitions.Def_SingleMachinePrec_IntervalReduction_TreeLayout
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


def GPVertex.equivSum (L : TreeLayout G) :
    GPVertex L ≃ Fin N ⊕ Fin N ⊕ Fin N ⊕ NonTreeEdge L ⊕ NonTreeEdge L where
  toFun
    | .v i => .inl i
    | .u1 i => .inr (.inl i)
    | .u2 i => .inr (.inr (.inl i))
    | .e1 q => .inr (.inr (.inr (.inl q)))
    | .e2 q => .inr (.inr (.inr (.inr q)))
  invFun
    | .inl i => .v i
    | .inr (.inl i) => .u1 i
    | .inr (.inr (.inl i)) => .u2 i
    | .inr (.inr (.inr (.inl q))) => .e1 q
    | .inr (.inr (.inr (.inr q))) => .e2 q
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with i | i | i | q | q <;> rfl

noncomputable instance GPVertex.instFintype (L : TreeLayout G) : Fintype (GPVertex L) :=
  Fintype.ofEquiv _ (GPVertex.equivSum L).symm

lemma card_dec (L : TreeLayout G) (C : Finset (GPVertex L)) :
    C.card = (Finset.univ.filter (fun i : Fin N => GPVertex.v i ∈ C)).card
      + (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C)).card
      + (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C)).card
      + (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C)).card
      + (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C)).card := by
  have h1 : C.card = ∑ x : GPVertex L, if x ∈ C then 1 else 0 := by
    rw [← Finset.card_filter]; congr 1; ext x; simp
  rw [h1, Fintype.sum_equiv (GPVertex.equivSum L) _ (fun s => if (GPVertex.equivSum L).symm s ∈ C then 1 else 0)
    (by intro x; simp)]
  simp only [Fintype.sum_sum_type, Finset.card_filter]
  simp only [GPVertex.equivSum, Equiv.coe_fn_symm_mk, add_assoc]
  congr!

open Classical in
lemma cl1_up (L : TreeLayout G) (C0 : Finset (Fin N)) (hC0 : G.IsVertexCover (C0 : Set (Fin N))) :
    ∃ C' : Finset (GPVertex L), (GPrime L).IsVertexCover (C' : Set (GPVertex L)) ∧
      C'.card = C0.card + N + Fintype.card (NonTreeEdge L) := by
  let P : GPVertex L → Prop := fun x => match x with
    | .v i => i ∈ C0
    | .u2 i => i ∈ C0
    | .u1 i => i ∉ C0
    | .e1 q => q.1.2 ∈ C0
    | .e2 q => q.1.2 ∉ C0
  refine ⟨Finset.univ.filter P, ?_, ?_⟩
  · intro x y hxy
    rw [GPrime, SimpleGraph.fromRel_adj] at hxy
    obtain ⟨hne, h⟩ := hxy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rcases h with h | h <;> cases x <;> cases y <;> simp only [gpRel] at h <;> simp only [P]
    all_goals first
      | exact hC0 (L.par_adj _ _ h)
      | exact (hC0 (L.par_adj _ _ h)).symm
      | (subst h; tauto)
      | (subst h; exact hC0 (‹NonTreeEdge L›).2.2.1)
      | (subst h; exact (hC0 (‹NonTreeEdge L›).2.2.1).symm)
  · rw [card_dec]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]
    have h1 : (Finset.univ.filter (fun i : Fin N => i ∈ C0)) = C0 := by ext; simp
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun i : Fin N => i ∈ C0)
    have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (NonTreeEdge L)))
      (fun q : NonTreeEdge L => q.1.2 ∈ C0)
    rw [h1] at h2 ⊢
    simp only [Finset.card_univ, Fintype.card_fin] at h2 h3
    omega

open Classical in
lemma cl1_low (L : TreeLayout G) (C' : Finset (GPVertex L))
    (hC' : (GPrime L).IsVertexCover (C' : Set (GPVertex L))) :
    ∃ C0 : Finset (Fin N), G.IsVertexCover (C0 : Set (Fin N)) ∧
      C0.card + N + Fintype.card (NonTreeEdge L) ≤ C'.card := by
  have hadj : ∀ x y, gpRel L x y → x ∈ C' ∨ y ∈ C' := by
    intro x y h
    have : (GPrime L).Adj x y := by
      rw [GPrime, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl h⟩
      rintro rfl
      cases x <;> simp only [gpRel] at h
      exact lt_irrefl _ (L.par_lt _ _ h)
    exact hC' this
  set A : Finset (Fin N) := Finset.univ.filter (fun i => GPVertex.v i ∈ C') with hA
  set B : Finset (Fin N) := Finset.univ.filter (fun i => GPVertex.u1 i ∈ C' ∧ GPVertex.u2 i ∈ C') with hB
  set Q2 : Finset (NonTreeEdge L) :=
    Finset.univ.filter (fun q => GPVertex.e1 q ∈ C' ∧ GPVertex.e2 q ∈ C') with hQ2
  refine ⟨A ∪ B ∪ Q2.image (fun q => q.1.1), ?_, ?_⟩
  · have key : ∀ a b, G.Adj a b → a < b → a ∈ A ∪ B ∪ Q2.image (fun q => q.1.1) ∨
        b ∈ A ∪ B ∪ Q2.image (fun q => q.1.1) := by
      intro a b hab hlt
      by_cases hp : L.par b = some a
      · rcases hadj (.v a) (.v b) hp with h | h
        · left; simp [hA, h]
        · right; simp [hA, h]
      · let q : NonTreeEdge L := ⟨(a, b), hlt, hab, hp⟩
        by_contra hcon
        push_neg at hcon
        obtain ⟨ha, hb⟩ := hcon
        have h1 : GPVertex.v a ∉ C' := fun h => ha (by simp [hA, h])
        have h2 : GPVertex.v b ∉ C' := fun h => hb (by simp [hA, h])
        have h3 : ¬ (GPVertex.e1 q ∈ C' ∧ GPVertex.e2 q ∈ C') := fun h =>
          ha (by simp only [Finset.mem_union, Finset.mem_image]; right; exact ⟨q, by simp [hQ2, h], rfl⟩)
        have h4 : ¬ (GPVertex.u1 b ∈ C' ∧ GPVertex.u2 b ∈ C') := fun h =>
          hb (by simp [hB, h])
        have e1 : GPVertex.e1 q ∈ C' := by
          rcases hadj (.v a) (.e1 q) rfl with h | h
          · exact absurd h h1
          · exact h
        have e2 : GPVertex.e2 q ∉ C' := fun h => h3 ⟨e1, h⟩
        have e3 : GPVertex.u2 b ∈ C' := by
          rcases hadj (.e2 q) (.u2 b) rfl with h | h
          · exact absurd h e2
          · exact h
        have e4 : GPVertex.u1 b ∉ C' := fun h => h4 ⟨h, e3⟩
        rcases hadj (.u1 b) (.v b) rfl with h | h
        · exact e4 h
        · exact h2 h
    intro a b hab
    rcases lt_or_gt_of_ne hab.ne with h | h
    · exact key a b hab h
    · exact (key b a hab.symm h).symm
  · have hc := card_dec L C'
    have hU : (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C')).card +
        (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C')).card = N + B.card := by
      have := Finset.card_union_add_card_inter (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C'))
        (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C'))
      have hu : (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C')) ∪
          (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C')) = Finset.univ := by
        ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        rcases hadj (.u2 i) (.u1 i) rfl with h | h
        · right; exact h
        · left; exact h
      have hi : (Finset.univ.filter (fun i : Fin N => GPVertex.u1 i ∈ C')) ∩
          (Finset.univ.filter (fun i : Fin N => GPVertex.u2 i ∈ C')) = B := by
        ext i; simp [hB]
      rw [hu, hi] at this
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hE : (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C')).card +
        (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C')).card =
        Fintype.card (NonTreeEdge L) + Q2.card := by
      have := Finset.card_union_add_card_inter (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C'))
        (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C'))
      have hu : (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C')) ∪
          (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C')) = Finset.univ := by
        ext q
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact hadj (.e1 q) (.e2 q) rfl
      have hi : (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e1 q ∈ C')) ∩
          (Finset.univ.filter (fun q : NonTreeEdge L => GPVertex.e2 q ∈ C')) = Q2 := by
        ext q; simp [hQ2]
      rw [hu, hi] at this
      simp only [Finset.card_univ] at this
      omega
    have hAc : A.card = (Finset.univ.filter (fun i : Fin N => GPVertex.v i ∈ C')).card := rfl
    have h1 : (A ∪ B ∪ Q2.image (fun q => q.1.1)).card ≤ A.card + B.card + Q2.card :=
      (Finset.card_union_le _ _).trans
        (add_le_add (Finset.card_union_le _ _) Finset.card_image_le)
    omega

lemma vc_exists' {V : Type*} [Finite V] (H : SimpleGraph V) :
    ∃ D : Finset V, H.IsVertexCover (D : Set V) ∧ (D.card : ℕ∞) = H.vertexCoverNum := by
  obtain ⟨s, hs1, hs2⟩ := SimpleGraph.vertexCoverNum_exists H
  refine ⟨(Set.toFinite s).toFinset, by simpa using hs2, ?_⟩
  rw [← hs1, ← Set.encard_coe_eq_coe_finsetCard]; simp

lemma vc_le_card' {V : Type*} (H : SimpleGraph V) (D : Finset V) (hD : H.IsVertexCover (D : Set V)) :
    H.vertexCoverNum ≤ (D.card : ℕ∞) := by
  have := hD.vertexCoverNum_le
  rwa [Set.encard_coe_eq_coe_finsetCard] at this

theorem claim1_core {N : ℕ} (G : SimpleGraph (Fin N)) (L : TreeLayout G) :
    (GPrime L).vertexCoverNum =
      G.vertexCoverNum + (N : ℕ∞) + (Fintype.card (NonTreeEdge L) : ℕ∞) := by
  obtain ⟨C0, hC0, hC0c⟩ := vc_exists' G
  obtain ⟨C1, hC1, hC1c⟩ := vc_exists' (GPrime L)
  obtain ⟨C', hC', hC'c⟩ := cl1_up L C0 hC0
  obtain ⟨C2, hC2, hC2c⟩ := cl1_low L C1 hC1
  have h1 : (GPrime L).vertexCoverNum ≤ (C'.card : ℕ∞) := vc_le_card' _ _ hC'
  have h2 : G.vertexCoverNum ≤ (C2.card : ℕ∞) := vc_le_card' _ _ hC2
  rw [← hC0c]
  apply le_antisymm
  · rw [hC'c] at h1; exact_mod_cast h1
  · rw [← hC1c]
    have : C0.card ≤ C2.card := by
      have := h2; rw [← hC0c] at this; exact_mod_cast this
    exact_mod_cast (by omega : C0.card + N + Fintype.card (NonTreeEdge L) ≤ C1.card)


lemma parNum_le_val (L : TreeLayout G) (j : Fin N) : parNum L j ≤ j.val := by
  unfold parNum
  cases h : L.par j with
  | none => simp
  | some i' =>
    have h2 : i'.val < j.val := L.par_lt j i' h
    simp; omega

lemma par_iff (L : TreeLayout G) (j i : Fin N) : L.par j = some i ↔ parNum L j = i.val + 1 :=
  (parNum_eq_num L j i).symm

def l2 (L : TreeLayout G) : Job L → ℤ
  | .s0 => -2
  | .s j => 2 * (parNum L j : ℤ)
  | .m i => 2 * ((i.val : ℤ) + 1) - 1
  | .e i => 2 * ((N : ℤ) + (i.val + 1))
  | .b q => 2 * ((q.1.1.val : ℤ) + 1)

def r2 (L : TreeLayout G) : Job L → ℤ
  | .s0 => 0
  | .s j => 2 * ((j.val : ℤ) + 1)
  | .m i => 2 * ((N : ℤ) + (i.val + 1))
  | .e i => 2 * ((N : ℤ) + (i.val + 1)) + 2
  | .b q => 2 * ((q.1.2.val : ℤ) + 1) - 1

lemma left_eq (L : TreeLayout G) (x : Job L) : left L x = (l2 L x : ℝ) / 2 := by
  cases x <;> simp [left, l2, num] <;> ring

lemma right_eq (L : TreeLayout G) (x : Job L) : right L x = (r2 L x : ℝ) / 2 := by
  cases x <;> simp [right, r2, num] <;> ring

lemma le_iff (L : TreeLayout G) (x y : Job L) : x ≤ y ↔ x = y ∨ r2 L x < l2 L y := by
  show (x = y ∨ right L x < left L y) ↔ _
  rw [right_eq, left_eq, div_lt_div_iff_of_pos_right (by norm_num)]
  simp

lemma vcg_adj (L : TreeLayout G) (u v : IncPair (prec L)) :
    (vertexCoverGraph (prec L)).Adj u v ↔
      u.1 ≠ v.1 ∧ u.1.1 ≤ v.1.2 ∧ v.1.1 ≤ u.1.2 := by
  show (u ≠ v ∧ (csRule (prec L) u v ∨ csRule (prec L) v u)) ↔ _
  have hne : u ≠ v ↔ u.1 ≠ v.1 :=
    ⟨fun h h' => h (Subtype.ext h'), fun h h' => h (congrArg Subtype.val h')⟩
  rw [hne]
  have hp : ∀ x y : Job L, prec L x y ↔ x ≤ y := fun _ _ => Iff.rfl
  have h1 : ∀ u v : IncPair (prec L), csRule (prec L) u v ↔ u.1.1 ≤ v.1.2 ∧ v.1.1 ≤ u.1.2 := by
    intro u v
    unfold csRule
    simp only [hp]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h2.le, h1.symm.le⟩
      · exact ⟨h2, h1.symm.le⟩
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact Or.inr (Or.inr ⟨h1, h2⟩)
  rw [h1, h1]
  constructor
  · rintro ⟨h, h' | h'⟩
    · exact ⟨h, h'⟩
    · exact ⟨h, h'.2, h'.1⟩
  · rintro ⟨h, h'⟩; exact ⟨h, Or.inl h'⟩


def parJob (L : TreeLayout G) (j : Fin N) : Job L :=
  match L.par j with
  | none => .s0
  | some i => .s i

lemma parJob_eq_s (L : TreeLayout G) (j i : Fin N) : parJob L j = .s i ↔ L.par j = some i := by
  unfold parJob
  cases h : L.par j <;> simp

lemma parJob_ne_s0 (L : TreeLayout G) (j : Fin N) : parJob L j = .s0 ↔ L.par j = none := by
  unfold parJob
  cases h : L.par j <;> simp

lemma parJob_ne_m (L : TreeLayout G) (j i : Fin N) : parJob L j ≠ .m i := by
  unfold parJob
  cases h : L.par j <;> simp
lemma parJob_ne_e (L : TreeLayout G) (j i : Fin N) : parJob L j ≠ .e i := by
  unfold parJob
  cases h : L.par j <;> simp
lemma parJob_ne_b (L : TreeLayout G) (j : Fin N) (q : NonTreeEdge L) : parJob L j ≠ .b q := by
  unfold parJob
  cases h : L.par j <;> simp

lemma r2_parJob (L : TreeLayout G) (j : Fin N) : r2 L (parJob L j) = 2 * (parNum L j : ℤ) := by
  unfold parJob parNum
  cases h : L.par j <;> simp [r2]

lemma l2_parJob_le (L : TreeLayout G) (j : Fin N) : l2 L (parJob L j) ≤ 2 * (j.val : ℤ) := by
  unfold parJob
  cases h : L.par j with
  | none => simp [l2]; omega
  | some i =>
    have h2 : i.val < j.val := L.par_lt j i h
    have := parNum_le_val L i
    simp only [l2]; omega

def pairOf (L : TreeLayout G) : GPVertex L → Job L × Job L
  | .v j => (parJob L j, .s j)
  | .u1 i => (.s i, .m i)
  | .u2 i => (.m i, .e i)
  | .e1 q => (.s q.1.1, .b q)
  | .e2 q => (.b q, .m q.1.2)

lemma nte_eq (L : TreeLayout G) (q q' : NonTreeEdge L) :
    q = q' ↔ q.1.1.val = q'.1.1.val ∧ q.1.2.val = q'.1.2.val := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply Subtype.ext
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)

lemma pj_and (L : TreeLayout G) (i j : Fin N) : (parJob L i = parJob L j ∧ i = j) ↔ i = j :=
  ⟨fun h => h.2, fun h => ⟨by rw [h], h⟩⟩

lemma pairOf_adj (L : TreeLayout G) (x y : GPVertex L) :
    (GPrime L).Adj x y ↔
      pairOf L x ≠ pairOf L y ∧ (pairOf L x).1 ≤ (pairOf L y).2 ∧ (pairOf L y).1 ≤ (pairOf L x).2 := by
  rw [GPrime, SimpleGraph.fromRel_adj]
  rcases x with i | i | i | q | q <;>
  rcases y with j | j | j | q' | q' <;>
  simp only [gpRel, pairOf, ne_eq, Prod.mk.injEq, le_iff, GPVertex.v.injEq, GPVertex.u1.injEq, GPVertex.u2.injEq, GPVertex.e1.injEq, GPVertex.e2.injEq, parJob_eq_s, par_iff, r2_parJob, Job.s.injEq, Job.m.injEq, Job.e.injEq, Job.b.injEq, reduceCtorEq, false_or, or_false, and_false, false_and, not_false_eq_true, true_and, and_true, parJob_ne_m, parJob_ne_e, parJob_ne_b, pj_and] <;>
  simp only [r2, l2, nte_eq, Fin.ext_iff, false_iff, iff_false] <;>
  (try have := parNum_le_val L i) <;> (try have := parNum_le_val L j) <;>
  (try have := Fin.lt_def.mp q.2.1) <;> (try have := Fin.lt_def.mp q'.2.1) <;>
  (try have := parNum_le_val L q.1.1) <;> (try have := parNum_le_val L q'.1.1) <;>
  (try have := parNum_le_val L q.1.2) <;> (try have := parNum_le_val L q'.1.2) <;>
  (try have := i.2) <;> (try have := j.2) <;> (try have := q.1.1.2) <;> (try have := q.1.2.2) <;>
  (try have := q'.1.1.2) <;> (try have := q'.1.2.2)
  all_goals omega


lemma s_eq_parJob (L : TreeLayout G) (j i : Fin N) : Job.s i = parJob L j ↔ L.par j = some i := by
  rw [eq_comm]; exact parJob_eq_s L j i

lemma pairOf_inc (L : TreeLayout G) (x : GPVertex L) :
    Incomparable (prec L) (pairOf L x).1 (pairOf L x).2 := by
  unfold Incomparable prec
  rcases x with i | i | i | q | q <;>
  simp only [pairOf, le_iff, parJob_eq_s, s_eq_parJob, par_iff, r2_parJob, Job.s.injEq, Job.m.injEq, Job.e.injEq,
    Job.b.injEq, reduceCtorEq, false_or, or_false, parJob_ne_m, parJob_ne_e, parJob_ne_b, not_or] <;>
  (try have h6 := l2_parJob_le L i) <;> (try generalize l2 L (parJob L i) = t at h6 ⊢) <;>
  simp only [r2, l2, Fin.ext_iff] <;>
  (try have := parNum_le_val L i) <;>
  (try have := Fin.lt_def.mp q.2.1) <;>
  (try have := i.2) <;> (try have := q.1.1.2) <;> (try have := q.1.2.2) <;>
  (try have := parNum_le_val L q.1.1) <;> (try have := parNum_le_val L q.1.2) <;>
  (try have h5 := L.par_lt i) <;>
  all_goals omega


lemma pairOf_inD (L : TreeLayout G) (x : GPVertex L) :
    InD L (pairOf L x).1 (pairOf L x).2 := by
  rcases x with j | i | i | q | q
  · cases h : L.par j <;> simp [pairOf, parJob, InD, h]
  · simp [pairOf, InD]
  · simp [pairOf, InD]
  · simp [pairOf, InD]
  · simp [pairOf, InD]

lemma pairOf_inj (L : TreeLayout G) : Function.Injective (pairOf L) := by
  intro x y h
  rcases x with i | i | i | q | q <;> rcases y with j | j | j | q' | q' <;>
    simp [pairOf] at h ⊢ <;> try (first | exact h | exact h.2 | exact h.1)

def Fmap (L : TreeLayout G) (x : GPVertex L) : {u : IncPair (prec L) | InD L u.1.1 u.1.2} :=
  ⟨⟨pairOf L x, pairOf_inc L x⟩, pairOf_inD L x⟩

lemma Fmap_surj (L : TreeLayout G) : Function.Surjective (Fmap L) := by
  rintro ⟨⟨⟨a, b⟩, hinc⟩, hD⟩
  have hD' : InD L a b := hD
  cases a <;> cases b <;> simp only [InD] at hD' <;> try contradiction
  · rename_i j
    refine ⟨.v j, Subtype.ext (Subtype.ext ?_)⟩
    show pairOf L (.v j) = (Job.s0, Job.s j)
    simp [pairOf, (parJob_ne_s0 L _).mpr hD']
  · rename_i i j
    refine ⟨.v j, Subtype.ext (Subtype.ext ?_)⟩
    show pairOf L (.v j) = (Job.s i, Job.s j)
    simp [pairOf, (parJob_eq_s L _ _).mpr hD']
  · subst hD'
    exact ⟨.u1 _, rfl⟩
  · subst hD'
    exact ⟨.e1 _, rfl⟩
  · subst hD'
    exact ⟨.u2 _, rfl⟩
  · subst hD'
    exact ⟨.e2 _, rfl⟩

noncomputable def isoG (L : TreeLayout G) : GPrime L ≃g GIprime L where
  toEquiv := Equiv.ofBijective (Fmap L)
    ⟨fun x y h => pairOf_inj L (congrArg (fun u => u.1.1) h), Fmap_surj L⟩
  map_rel_iff' := by
    intro x y
    show (vertexCoverGraph (prec L)).Adj (Fmap L x).1 (Fmap L y).1 ↔ _
    rw [vcg_adj]
    exact (pairOf_adj L x y).symm

theorem claim3_core {N : ℕ} {G : SimpleGraph (Fin N)} (L : TreeLayout G) :
    Nonempty (GIprime L ≃g GPrime L) := ⟨(isoG L).symm⟩


theorem t71_core {N : ℕ} (G : SimpleGraph (Fin N)) (L : TreeLayout G) (m : ℕ) :
    AppliedComb.Posets.IsIntervalOrder (Job L) ∧
    ((∃ C : Finset (Fin N), G.IsVertexCover (C : Set (Fin N)) ∧ C.card ≤ m) ↔
      ⌊tauW L⌋₊ ≤ m + N + Fintype.card (NonTreeEdge L)) := by
  refine ⟨⟨left L, right L, left_le_right L, fun x y => ?_⟩, ?_⟩
  · rw [lt_iff_le_not_ge]
    show (x = y ∨ right L x < left L y) ∧ ¬ (y = x ∨ right L y < left L x) ↔ _
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1.symm) h2
      · exact h1
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (h2 | h2)
      · subst h2; linarith [left_le_right L y]
      · linarith [left_le_right L y, left_le_right L x]
  · obtain e := (claim3_core L).some
    have h1 := (lw_core L).2
    have hiso : (GIprime L).vertexCoverNum = (GPrime L).vertexCoverNum := by
      apply le_antisymm
      · exact SimpleGraph.IsContained.vertexCoverNum_le_vertexCoverNum ⟨e.toHom, e.injective⟩
      · exact SimpleGraph.IsContained.vertexCoverNum_le_vertexCoverNum ⟨e.symm.toHom, e.symm.injective⟩
    have h2 := claim1_core G L
    obtain ⟨D, hD, hDc⟩ := vc_exists' G
    have hfin : G.vertexCoverNum ≠ ⊤ := SimpleGraph.vertexCoverNum_ne_top_of_finite
    obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp hfin
    have h3 : ((⌊tauW L⌋₊ : ℕ) : ℕ∞) = ((c + N + Fintype.card (NonTreeEdge L) : ℕ) : ℕ∞) := by
      rw [← h1, hiso, h2, ← hc]; push_cast; rfl
    have h4 : ⌊tauW L⌋₊ = c + N + Fintype.card (NonTreeEdge L) := by exact_mod_cast h3
    rw [h4]
    constructor
    · rintro ⟨C, hC, hCm⟩
      have := vc_le_card' G C hC
      rw [← hc] at this
      have : c ≤ C.card := by exact_mod_cast this
      omega
    · intro h
      refine ⟨D, hD, ?_⟩
      rw [← hc] at hDc
      have : D.card = c := by exact_mod_cast hDc
      omega

end SingleMachinePrec.IntervalReduction

open SingleMachinePrec.IntervalReduction


theorem solution {N : ℕ} (G : SimpleGraph (Fin N)) (hconn : G.Connected)
    (hdeg : ∀ v, (G.neighborSet v).ncard ≤ 3) (L : TreeLayout G) (m : ℕ) :
    AppliedComb.Posets.IsIntervalOrder (Job L) ∧
    ((∃ C : Finset (Fin N), G.IsVertexCover (C : Set (Fin N)) ∧ C.card ≤ m) ↔
      ⌊tauW L⌋₊ ≤ m + N + Fintype.card (NonTreeEdge L)) := by
  exact t71_core G L m
