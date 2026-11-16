-- Prove2me | solution 1 for RGMISFast.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-15T22:04:19.215968+00:00
-- url     : https://prove2.me/submissions/d52d1d0d-882d-403a-ba5e-27b4ff8efd22

import Definitions.Def_RGMISFast_AdmissibleTree
import Definitions.Def_RGMISFast_GoodEvent
set_option autoImplicit false

namespace P41Proposition42Scalars
open RGMISFast
set_option autoImplicit false

 theorem band_factor_gt_one : 1 < c := by
  unfold c
  have hp := Real.exp_pos 2
  have h : 0 < 1 / (2 * Real.exp 2) := by positivity
  linarith

 theorem band_factor_power_85 : (256 : ℝ) ≤ c ^ (85 : ℕ) := by
  have he1 := Real.exp_one_lt_d9
  have hepos := Real.exp_pos 1
  have he2 : Real.exp 2 < (37 / 5 : ℝ) := by
    have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [heq]
    nlinarith
  have hden : 0 < 2 * Real.exp 2 := by positivity
  have hc : (79 / 74 : ℝ) ≤ c := by
    unfold c
    have hi : (5 / 74 : ℝ) ≤ 1 / (2 * Real.exp 2) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    linarith
  have hnum : (256 : ℝ) ≤ (79 / 74 : ℝ) ^ (85 : ℕ) := by norm_num
  exact hnum.trans (pow_le_pow_left₀ (by norm_num) hc _)

 theorem band_growth_integral_power (m : ℕ) :
    (256 : ℝ)^m ≤ (c^m)^85 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 256) band_factor_power_85 m
  simpa only [← pow_mul, Nat.mul_comm] using h

 theorem prefix_factor_le_degree_power (m : ℕ) (K Δ : ℝ)
    (hK : 0 ≤ K) (hΔ : 0 ≤ Δ) (hband : c^m ≤ K*Δ) :
    (a0 / am m)^3 * (256 : ℝ)^m ≤ K^88 * Δ^88 := by
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  have ha : 0 < a0 := Real.exp_pos 2
  have hid : a0 / am m = c^m := by
    unfold am
    field_simp
  rw [hid]
  calc
    _ ≤ (c^m)^3 * (c^m)^85 := mul_le_mul_of_nonneg_left (band_growth_integral_power m) (by positivity)
    _ = (c^m)^88 := by rw [← pow_add]
    _ ≤ (K*Δ)^88 := pow_le_pow_left₀ (by positivity) hband _
    _ = K^88 * Δ^88 := mul_pow _ _ _

/-- Appendix C, equations (38)--(39), including the exact factor 1285. -/
theorem appendix_c_recurrence (X : ℕ → ℝ) (L : ℝ)
    (h0 : X 0 ≤ 5*L)
    (hstep : ∀ m : ℕ, X (m+1) ≤ 255 * ∑ i ∈ Finset.range (m+1), X i + 10*L) :
    ∀ m : ℕ, X (m+1) ≤ 1285*L*(256:ℝ)^m := by
  have hsum : ∀ m : ℕ, (∑ i ∈ Finset.range (m+1), X i) ≤
      ((1285*(256:ℝ)^m - 10)/255)*L := by
    intro m
    induction m with
    | zero => norm_num; exact h0
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep m
      have hmul := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ) ≤ 256)
      rw [pow_succ]
      nlinarith
  intro m
  have hs := hstep m
  have hb := hsum m
  nlinarith

lemma band_positive (m : ℕ) : 0 < am m := by
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  unfold am a0
  positivity

lemma band_antitone : Antitone am := by
  intro i j hij
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  unfold am
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 2).le
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ band_factor_gt_one.le hij)

lemma terminal_band_power (Δ : ℕ) (hΔ : 2 ≤ Δ) :
    c ^ Mof Δ ≤ (16*a0*c)*(Δ : ℝ) := by
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  have ha : 0 < a0 := Real.exp_pos 2
  have hd : 0 < (Δ : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hΔ)
  have hne : Set.Nonempty {m : ℕ | am m ≤ 1/(16*(Δ:ℝ))} := by
    obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (16*a0*(Δ:ℝ)) band_factor_gt_one
    refine ⟨m, ?_⟩
    change a0*(c^m)⁻¹ ≤ 1/(16*(Δ:ℝ))
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  by_cases hz : Mof Δ = 0
  · rw [hz, pow_zero]
    have ha1 : 1 ≤ a0 := by exact Real.one_le_exp (by norm_num)
    have hd1 : 1 ≤ (Δ:ℝ) := by exact_mod_cast (by omega : 1 ≤ Δ)
    have hp := mul_le_mul ha1 band_factor_gt_one.le (by norm_num : (0:ℝ) ≤ 1) ha.le
    have hp2 := mul_le_mul_of_nonneg_right hp hd.le
    nlinarith
  · obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hz
    have hnot : ¬ am m ≤ 1/(16*(Δ:ℝ)) := by
      intro ht
      have hle : Mof Δ ≤ m := csInf_le (OrderBot.bddBelow _) ht
      omega
    have hbound : c^m < 16*a0*(Δ:ℝ) := by
      have hh := lt_of_not_ge hnot
      change 1/(16*(Δ:ℝ)) < a0 / c^m at hh
      have hh' := (div_lt_div_iff₀ (by positivity : 0 < 16*(Δ:ℝ))
        (by positivity : 0 < c^m)).mp hh
      nlinarith
    rw [hm, pow_succ]
    nlinarith [mul_lt_mul_of_pos_right hbound hc]

lemma band_previous (m : ℕ) (hm : 1 ≤ m) : am (m-1) = c*am m := by
  have hc : c ≠ 0 := (lt_trans (by norm_num) band_factor_gt_one).ne'
  have he : c^m = c^(m-1)*c := by rw [← pow_succ]; congr 1; omega
  unfold am
  rw [he]
  field_simp

lemma cap_rank_band {V : Type*} (r : V → ℝ) (v : V) (i : ℕ)
    (hv : (r v : WithTop ℝ) < b i) : rbar r v ≤ c*am i := by
  by_cases hi : i = 0
  · subst i
    have ha : 0 ≤ a0 := (Real.exp_pos 2).le
    have hc := mul_le_mul_of_nonneg_right band_factor_gt_one.le ha
    simp only [am, pow_zero, inv_one, mul_one] at *
    exact (min_le_right _ _).trans (by linarith)
  · have hv' : r v < am (i-1) := by simpa [b, hi] using hv
    rw [band_previous i (by omega)] at hv'
    exact (min_le_left _ _).trans hv'.le

lemma band_factor_le_eleven_tenths : c ≤ (11/10:ℝ) := by
  have he : 5 ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (1:ℝ)
    have he1 := Real.exp_one_gt_two
    have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have he2 := Real.exp_one_gt_d9
    rw [heq]
    nlinarith
  unfold c
  have hp : 0 < 2*Real.exp 2 := by positivity
  have hh : 1/(2*Real.exp 2) ≤ (1/10:ℝ) := (div_le_iff₀ hp).mpr (by linarith)
  linarith

lemma recurrence_coefficient_bound : (1+2*c)*(1+64*c^2) ≤ 255 := by
  have hc : 0 ≤ c := (lt_trans (by norm_num) band_factor_gt_one).le
  have hh := band_factor_le_eleven_tenths
  have hs : c^2 ≤ (11/10:ℝ)^2 := pow_le_pow_left₀ hc hh 2
  have hp := mul_le_mul (show 1+2*c ≤ (16/5:ℝ) by linarith)
    (show 1+64*c^2 ≤ (1961/25:ℝ) by nlinarith)
    (by positivity : 0 ≤ 1+64*c^2) (by norm_num : (0:ℝ) ≤ 16/5)
  linarith
end P41Proposition42Scalars
open P41Proposition42Scalars

namespace P41AdmissibleGeometry
open RGMISFast
set_option autoImplicit false

 theorem settling_le_rank {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (v : V) :
    tau G r v ≤ r v := by
  classical
  by_cases hv : inMIS G r v = true
  · apply Finset.min'_le
    exact Finset.mem_image.mpr ⟨v, by simp [hv], rfl⟩
  · have he := inMIS_eq G r v
    have hvf : inMIS G r v = false := Bool.eq_false_iff.mpr hv
    rw [hvf] at he
    obtain ⟨w, _, hw⟩ := List.all_eq_false.mp he.symm
    have hwyes : inMIS G r w.val = true := by simpa using hw
    have ha := (mem_lowerNbrs G r).1 w.property
    have hmin : tau G r v ≤ r w.val := by
      apply Finset.min'_le
      exact Finset.mem_image.mpr ⟨w.val, by simp [ha.1,hwyes], rfl⟩
    exact hmin.trans ha.2.le

 theorem ancestor_closed_connected {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (u : V)
    (T : AdmissibleTree G r u) (S : Finset V) (hS : S ⊆ T.nodes)
    (hne : S.Nonempty) (hpar : ∀ w ∈ S, w ≠ u → T.par w ∈ S) :
    IsRootConnected G u S := by
  have hall : ∀ n, ∀ w ∈ S, T.depth w = n → u ∈ S ∧ (restrictTo G ↑S).Reachable u w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw hd
      by_cases he : w = u
      · subst w
        exact ⟨hw,SimpleGraph.Reachable.refl _⟩
      · have hp := hpar w hw he
        obtain ⟨hu,hr⟩ := ih (T.depth (T.par w)) (by simpa [hd] using T.depth_lt w (hS hw) he)
          (T.par w) hp rfl
        refine ⟨hu,hr.trans ?_⟩
        exact SimpleGraph.Adj.reachable (show (restrictTo G ↑S).Adj (T.par w) w from
          ⟨T.par_adj w (hS hw) he,hp,hw⟩)
  obtain ⟨w,hw⟩ := hne
  exact ⟨(hall _ w hw rfl).1,fun x hx => (hall _ x hx rfl).2⟩

 theorem prefix_connected {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (u : V)
    (T : AdmissibleTree G r u) (t : ℝ) (hne : (T.prefix t).Nonempty) :
    IsRootConnected G u (T.prefix t) := by
  apply ancestor_closed_connected G r u T (T.prefix t) (Finset.filter_subset _ _) hne
  intro w hw hwu
  obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨T.par_mem w hw hwu,
    ht.trans ((settling_le_rank G r w).trans (T.rank_le w hw hwu))⟩

 theorem prefix_active {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (u : V)
    (T : AdmissibleTree G r u) (t : ℝ) : ActiveAt G r t (T.prefix t) := by
  intro w hw
  exact (Finset.mem_filter.mp hw).2
end P41AdmissibleGeometry
open P41AdmissibleGeometry

namespace P41Proposition42Accounting
open RGMISFast
set_option autoImplicit false

noncomputable def treeFrontier {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (t : ℝ) : Finset V := by
  classical
  exact insert u (T.prefix t ∪ T.nodes.filter (fun w => w ≠ u ∧ T.par w ∈ T.prefix t))

lemma frontier_subset {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (t : ℝ) : treeFrontier T t ⊆ T.nodes := by
  classical
  intro w hw
  simp only [treeFrontier, Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hw
  rcases hw with rfl | h | h
  · exact T.root_mem
  · exact (Finset.mem_filter.mp h).1
  · exact h.1

lemma frontier_connected {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (t : ℝ) : IsRootConnected G u (treeFrontier T t) := by
  classical
  apply ancestor_closed_connected G r u T _ (frontier_subset T t)
    (Finset.insert_nonempty _ _)
  intro w hw hwu
  simp only [treeFrontier, Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hw ⊢
  rcases hw with he | hw | hw
  · exact (hwu he).elim
  · right; left
    obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr
    exact ⟨T.par_mem w hw hwu,
      ht.trans ((settling_le_rank G r w).trans (T.rank_le w hw hwu))⟩
  · exact Or.inr (Or.inl hw.2.2)

lemma outside_frontier_rank {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (t : ℝ) (w : V)
    (hw : w ∈ T.nodes) (hout : w ∉ treeFrontier T t) : r w < t := by
  classical
  have hwu : w ≠ u := by intro he; subst w; exact hout (by simp [treeFrontier])
  have hp : T.par w ∉ T.prefix t := by
    intro hp
    exact hout (by simp [treeFrontier, hw, hwu, hp])
  have ht : tau G r (T.par w) < t := by
    simpa [AdmissibleTree.prefix, T.par_mem w hw hwu] using hp
  exact (T.rank_le w hw hwu).trans_lt ht

lemma outside_frontier_in_gammaLow {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (Δ : ℕ) :
    T.nodes \ treeFrontier T (am (Mof Δ)) ⊆ GammaLow G r Δ (treeFrontier T (am (Mof Δ))) := by
  classical
  let A := treeFrontier T (am (Mof Δ))
  let S : Set V := {y | y ∈ A ∨ r y < am (Mof Δ)}
  have hin : ∀ w ∈ T.nodes, w ∈ S := by
    intro w hw
    by_cases ha : w ∈ A
    · exact Or.inl ha
    · exact Or.inr (outside_frontier_rank T _ w hw ha)
  have hpath : ∀ n, ∀ w ∈ T.nodes, T.depth w = n → (restrictTo G S).Reachable u w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw hd
      by_cases hwu : w = u
      · subst w; exact SimpleGraph.Reachable.refl _
      · have hp := T.par_mem w hw hwu
        have hr := ih _ (by simpa [hd] using T.depth_lt w hw hwu) _ hp rfl
        exact hr.trans (SimpleGraph.Adj.reachable ⟨T.par_adj w hw hwu, hin _ hp, hin _ hw⟩)
  intro w hw
  obtain ⟨hw,ha⟩ := Finset.mem_sdiff.mp hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, u, by simp [treeFrontier], hpath _ w hw rfl⟩

lemma frontier_card {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (t : ℝ) (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) :
    (treeFrontier T t).card ≤ (Δ+1)*(T.prefix t).card+1 := by
  classical
  let P := T.prefix t
  have hsub : T.nodes.filter (fun w => w ≠ u ∧ T.par w ∈ P) ⊆
      P.biUnion (fun v => G.neighborFinset v) := by
    intro w hw
    obtain ⟨hw, hwu, hp⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_biUnion.mpr ⟨T.par w, hp, by simpa using T.par_adj w hw hwu⟩
  have hb : (P.biUnion (fun v => G.neighborFinset v)).card ≤ P.card * Δ := by
    apply Finset.card_biUnion_le_card_mul
    intro x hx
    exact hdeg x
  have hh := (Finset.card_le_card hsub).trans hb
  have hi := Finset.card_insert_le u (P ∪ T.nodes.filter (fun w => w ≠ u ∧ T.par w ∈ P))
  have hu := Finset.card_union_le P (T.nodes.filter (fun w => w ≠ u ∧ T.par w ∈ P))
  change (insert u (P ∪ T.nodes.filter (fun w => w ≠ u ∧ T.par w ∈ P))).card ≤ _
  change _ ≤ (Δ+1)*P.card+1
  nlinarith

/-- The low-rank accounting in Proposition 4.2, with the additive deviation term. -/
theorem tree_card_from_frontier {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (Δ : ℕ) (L : ℝ)
    (hlow : LowRankEvent G Δ u L r) :
    (T.nodes.card : ℝ) ≤ (treeFrontier T (am (Mof Δ))).card *
      (1+2*Real.log (8*Real.exp 1*Δ))+2*L+4 := by
  classical
  have he := Finset.card_sdiff_add_card_eq_card (frontier_subset T (am (Mof Δ)))
  have hc : ((T.nodes \ treeFrontier T (am (Mof Δ))).card : ℝ) ≤
      (GammaLow G r Δ (treeFrontier T (am (Mof Δ)))).card := by
    exact_mod_cast Finset.card_le_card (outside_frontier_in_gammaLow T Δ)
  have hl := hlow _ (frontier_connected T (am (Mof Δ)))
  have her : ((T.nodes \ treeFrontier T (am (Mof Δ))).card : ℝ) +
      (treeFrontier T (am (Mof Δ))).card = T.nodes.card := by exact_mod_cast he
  nlinarith

lemma low_rank_log_factor (Δ : ℕ) (hΔ : 2 ≤ Δ) :
    1+2*Real.log (8*Real.exp 1*Δ) ≤ (1+16*Real.exp 1)*(Δ:ℝ) := by
  have hd : 1 ≤ (Δ:ℝ) := by exact_mod_cast (by omega : 1 ≤ Δ)
  have hp : 0 < 8*Real.exp 1*(Δ:ℝ) := by positivity
  have hh := Real.log_le_sub_one_of_pos hp
  nlinarith

/-- Complete final accounting from a degree-88 bound on the terminal prefix.
The prefix estimate is an explicit hypothesis, not an imported open theorem. -/
theorem tree_card_from_prefix_bound {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀ v, G.degree v ≤ Δ) (L B : ℝ) (hL : 1 ≤ L) (hB : 0 ≤ B)
    (hlow : LowRankEvent G Δ u L r)
    (hprefix : ((T.prefix (am (Mof Δ))).card : ℝ) ≤ B*L*(Δ:ℝ)^88) :
    (T.nodes.card : ℝ) ≤ ((2*B+1)*(1+16*Real.exp 1)+6)*L*(Δ:ℝ)^90 := by
  classical
  have hd : 1 ≤ (Δ:ℝ) := by exact_mod_cast (by omega : 1 ≤ Δ)
  have hd0 : 0 ≤ (Δ:ℝ) := by positivity
  have hL0 : 0 ≤ L := by linarith
  have hd89 : 1 ≤ (Δ:ℝ)^89 := one_le_pow₀ hd
  have hd90 : 1 ≤ (Δ:ℝ)^90 := one_le_pow₀ hd
  have ha : ((treeFrontier T (am (Mof Δ))).card : ℝ) ≤
      (2*B+1)*L*(Δ:ℝ)^89 := by
    have hc : ((treeFrontier T (am (Mof Δ))).card : ℝ) ≤
        ((Δ:ℝ)+1)*((T.prefix (am (Mof Δ))).card : ℝ)+1 := by
      exact_mod_cast frontier_card T (am (Mof Δ)) Δ hdeg
    have hs := mul_le_mul_of_nonneg_left hprefix (by positivity : 0 ≤ (Δ:ℝ)+1)
    have hb : 0 ≤ B*L*(Δ:ℝ)^88 := by positivity
    have hm := mul_le_mul_of_nonneg_right (show (Δ:ℝ)+1 ≤ 2*(Δ:ℝ) by linarith) hb
    have hunit : 1 ≤ L*(Δ:ℝ)^89 := one_le_mul_of_one_le_of_one_le hL hd89
    rw [pow_succ] at hunit ⊢
    nlinarith
  have ht := tree_card_from_frontier T Δ L hlow
  have hlog := low_rank_log_factor Δ hΔ
  have ht' := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ ((treeFrontier T (am (Mof Δ))).card : ℝ))
  have hh := mul_le_mul_of_nonneg_right ha
    (by positivity : 0 ≤ (1+16*Real.exp 1)*(Δ:ℝ))
  have hpow : 2*L+4 ≤ 6*L*(Δ:ℝ)^90 := by
    have hp := mul_le_mul_of_nonneg_left hd90 (show 0 ≤ 6*L by positivity)
    nlinarith
  calc
    _ ≤ ((2*B+1)*L*(Δ:ℝ)^89)*((1+16*Real.exp 1)*(Δ:ℝ)) +
        6*L*(Δ:ℝ)^90 := by linarith
    _ = _ := by rw [show (90:ℕ)=89+1 from rfl, pow_succ]; ring
end P41Proposition42Accounting
open P41Proposition42Accounting

namespace P41PrefixAccounting
open RGMISFast
set_option autoImplicit false

lemma prefix_mono {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) {i j : ℕ} (hij : i ≤ j) :
    T.prefix (am i) ⊆ T.prefix (am j) := by
  intro w hw
  obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hw,(band_antitone hij).trans ht⟩

lemma prefix_top_subset {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) : T.prefix a0 ⊆ C0 G r u := by
  classical
  intro w hw
  have hp := prefix_connected G r u T a0 ⟨w,hw⟩
  have hu : a0 ≤ tau G r u := (Finset.mem_filter.mp hp.1).2
  simp only [C0, if_pos hu, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(Finset.mem_filter.mp hw).2, (hp.2 w hw).mono ?_⟩
  intro x y hxy
  exact ⟨hxy.1,(Finset.mem_filter.mp hxy.2.1).2,(Finset.mem_filter.mp hxy.2.2).2⟩

lemma charge_nonneg {V : Type*} (r : V → ℝ) (hr : ∀ v, 0 ≤ r v)
    (A : Finset V) (m : ℕ) : 0 ≤ Sm r A m := by
  have ha := band_positive m
  unfold Sm S
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro v hv
  exact le_min (hr v) (Real.exp_pos 2).le

lemma charge_mono {V : Type*} (r : V → ℝ) (hr : ∀ v, 0 ≤ r v)
    (A B : Finset V) (hAB : A ⊆ B) (m : ℕ) : Sm r A m ≤ Sm r B m := by
  have ha := band_positive m
  unfold Sm S
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg hAB
  intro v hv hvA
  exact le_min (hr v) (Real.exp_pos 2).le

lemma charge_active_card {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ}
    (A : Finset V) (m : ℕ) (hact : ActiveAt G r (am m) A) :
    (A.card : ℝ) ≤ Sm r A m := by
  have ha := band_positive m
  have ham : am m ≤ a0 := by simpa [am] using band_antitone (Nat.zero_le m)
  have hs : (A.card : ℝ)*am m ≤ ∑ v ∈ A, rbar r v := by
    calc
      _ = ∑ v ∈ A, am m := by simp
      _ ≤ _ := Finset.sum_le_sum fun v hv =>
        le_min ((hact v hv).trans (settling_le_rank G r v)) ham
  unfold Sm S
  rw [one_div, ← div_eq_inv_mul]
  exact (le_div_iff₀ ha).mpr hs

lemma top_charge_card {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) : Sm r (T.prefix (am 0)) 0 = (T.prefix a0).card := by
  have ha : a0 ≠ 0 := (Real.exp_pos 2).ne'
  have he : am 0 = a0 := by simp [am]
  unfold Sm S
  rw [he]
  have hs : (∑ v ∈ T.prefix a0, rbar r v) = (T.prefix a0).card*a0 := by
    have hh : ∀ v ∈ T.prefix a0, rbar r v = a0 := by
      intro v hv
      exact min_eq_right ((Finset.mem_filter.mp hv).2.trans (settling_le_rank G r v))
    simp_rw [Finset.sum_congr rfl hh]
    simp
  rw [hs]
  field_simp

lemma top_charge_bound {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (L : ℝ) (htop : TopEvent G u L r) :
    Sm r (T.prefix (am 0)) 0 ≤ 1+L := by
  rw [top_charge_card]
  exact (Nat.cast_le.mpr (Finset.card_le_card (prefix_top_subset T))).trans htop

lemma charge_scale {V : Type*} (r : V → ℝ) (A : Finset V)
    {i m : ℕ} (him : i ≤ m) : Sm r A m = c^(m-i)*Sm r A i := by
  have hc : c ≠ 0 := (lt_trans (by norm_num) band_factor_gt_one).ne'
  have ha : a0 ≠ 0 := (Real.exp_pos 2).ne'
  have he : c^m = c^(m-i)*c^i := by rw [← pow_add, Nat.sub_add_cancel him]
  unfold Sm S am
  field_simp
  rw [he]
  ring

lemma charge_union_le {V : Type*} [DecidableEq V] (r : V → ℝ) (hr : ∀v, 0 ≤ r v)
    (A B : Finset V) (m : ℕ) : Sm r (A ∪ B) m ≤ Sm r A m + Sm r B m := by
  have ha := band_positive m
  have hsum : (∑v∈A ∪ B,rbar r v)+(∑v∈A ∩ B,rbar r v) =
      (∑v∈A,rbar r v)+(∑v∈B,rbar r v) := Finset.sum_union_inter
  have hpos : 0 ≤ ∑ v ∈ A ∩ B, rbar r v := Finset.sum_nonneg
    (fun v _ => le_min (hr v) (Real.exp_pos 2).le)
  unfold Sm S
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

lemma charge_biUnion_le {V I : Type*} [DecidableEq V] (r : V → ℝ) (hr : ∀v, 0 ≤ r v)
    (s : Finset I) (A : I → Finset V) (m : ℕ) :
    Sm r (s.biUnion A) m ≤ ∑ i ∈ s, Sm r (A i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Sm,S]
  | @insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (charge_union_le r hr _ _ m).trans (add_le_add le_rfl ih)

lemma charge_singleton_le {V : Type*} (r : V → ℝ) (u : V) (m : ℕ) :
    Sm r {u} m ≤ c^m := by
  have ha := band_positive m
  have ha0 : a0 ≠ 0 := (Real.exp_pos 2).ne'
  have hc : c ≠ 0 := (lt_trans (by norm_num) band_factor_gt_one).ne'
  unfold Sm S
  simp only [Finset.sum_singleton]
  calc
    _ ≤ (1/am m)*a0 := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
    _ = _ := by unfold am; field_simp

lemma charge_of_cap_bound {V : Type*} (r : V → ℝ) (A : Finset V) (m : ℕ)
    (q : ℝ) (hb : ∀v∈A, rbar r v ≤ q*am m) : Sm r A m ≤ q*A.card := by
  have ha := band_positive m
  have hs : (∑v∈A,rbar r v) ≤ A.card*(q*am m) := by
    simpa using Finset.sum_le_sum hb
  unfold Sm S
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1/am m by positivity)
  calc
    _ ≤ _ := hm
    _ = _ := by field_simp
end P41PrefixAccounting
open P41PrefixAccounting

namespace P41PrefixGeometry
open RGMISFast
set_option autoImplicit false

lemma frontier_parent {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (t : ℝ) (w : V)
    (hw : w ∈ treeFrontier T t) (hwu : w ≠ u) : T.par w ∈ treeFrontier T t := by
  classical
  simp only [treeFrontier, Finset.mem_insert, Finset.mem_union, Finset.mem_filter] at hw ⊢
  rcases hw with he | hw | hw
  · exact (hwu he).elim
  · right; left
    obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨T.par_mem w hw hwu,
      ht.trans ((settling_le_rank G r w).trans (T.rank_le w hw hwu))⟩
  · exact Or.inr (Or.inl hw.2.2)

noncomputable def bandFrontier {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (m : ℕ) : Finset V := by
  classical
  exact T.prefix (am m) ∩ treeFrontier T (am (m-1))

lemma bandFrontier_connected {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (m : ℕ) (hne : (T.prefix (am m)).Nonempty) :
    IsRootConnected G u (bandFrontier T m) := by
  classical
  have hu := (prefix_connected G r u T (am m) hne).1
  apply ancestor_closed_connected G r u T _
    (fun w hw => (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).1)
    ⟨u, Finset.mem_inter.mpr ⟨hu, by simp [treeFrontier]⟩⟩
  intro w hw hwu
  obtain ⟨hp,hf⟩ := Finset.mem_inter.mp hw
  obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨T.par_mem w hw hwu,
    ht.trans ((settling_le_rank G r w).trans (T.rank_le w hw hwu))⟩,
    frontier_parent T _ w hf hwu⟩

lemma bandFrontier_active {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (m : ℕ) : ActiveAt G r (am m) (bandFrontier T m) := by
  intro w hw
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2

lemma band_remainder_rank {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (m : ℕ) (w : V)
    (hw : w ∈ T.prefix (am m) \ bandFrontier T m) : r w < am (m-1) := by
  classical
  obtain ⟨hw,hn⟩ := Finset.mem_sdiff.mp hw
  apply outside_frontier_rank T _ w (Finset.mem_filter.mp hw).1
  intro hf
  exact hn (Finset.mem_inter.mpr ⟨hw,hf⟩)

lemma band_remainder_subset {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (m : ℕ) :
    T.prefix (am m) \ bandFrontier T m ⊆ Gammam G r m (bandFrontier T m) := by
  classical
  intro w hw
  have hp := prefix_connected G r u T (am m) ⟨w,(Finset.mem_sdiff.mp hw).1⟩
  have hact := bandFrontier_active T m
  simp only [Gammam, GammaAB, if_pos hact, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(Finset.mem_sdiff.mp hw).2,u,?_,(hp.2 w (Finset.mem_sdiff.mp hw).1).mono ?_⟩
  · simp [bandFrontier, treeFrontier, hp.1]
  · have hin : ∀y∈T.prefix (am m), y ∈ bandFrontier T m ∨
        (am m ≤ tau G r y ∧ (r y : WithTop ℝ) < (am (m-1) : ℝ)) := by
      intro y hy
      by_cases hf : y ∈ bandFrontier T m
      · exact Or.inl hf
      · exact Or.inr ⟨(Finset.mem_filter.mp hy).2,
          by exact_mod_cast band_remainder_rank T m y (Finset.mem_sdiff.mpr ⟨hy,hf⟩)⟩
    intro x y hxy
    exact ⟨hxy.1,hin x hxy.2.1,hin y hxy.2.2⟩

noncomputable def entryBoundary {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (m i : ℕ) : Finset V := by
  classical
  exact (outerBdry G (T.prefix (am i))).filter
    (fun w => am m ≤ tau G r w ∧ (r w : WithTop ℝ) < b i)

lemma bandFrontier_cover {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (m : ℕ) (hm : 1 ≤ m) :
    bandFrontier T m ⊆ {u} ∪ (T.prefix (am (m-1)) ∪
      (Finset.range m).biUnion (entryBoundary T m)) := by
  classical
  intro w hw
  obtain ⟨hwm,hwf⟩ := Finset.mem_inter.mp hw
  by_cases hwu : w = u
  · simp [hwu]
  by_cases hp : w ∈ T.prefix (am (m-1))
  · simp [hp]
  have hpar : T.par w ∈ T.prefix (am (m-1)) := by
    exact (by simpa [treeFrontier, hwu, hp] using hwf : w ∈ T.nodes ∧ T.par w ∈ T.prefix (am (m-1))).2
  have hex : ∃i, T.par w ∈ T.prefix (am i) := ⟨m-1,hpar⟩
  let i := Nat.find hex
  have hip : T.par w ∈ T.prefix (am i) := Nat.find_spec hex
  have hil : i < m := lt_of_le_of_lt (Nat.find_min' hex hpar) (by omega)
  have hwi : w ∉ T.prefix (am i) := by
    intro hh
    exact hp (prefix_mono T (by omega : i ≤ m-1) hh)
  have hrank : (r w : WithTop ℝ) < b i := by
    by_cases hi : i = 0
    · simp [b,hi]
    · have hprev : T.par w ∉ T.prefix (am (i-1)) := Nat.find_min hex (by omega)
      have hpt : tau G r (T.par w) < am (i-1) := by
        simpa [AdmissibleTree.prefix, (Finset.mem_filter.mp hip).1] using hprev
      have hr := (T.rank_le w (Finset.mem_filter.mp hwm).1 hwu).trans_lt hpt
      simpa [b,hi] using hr
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_range.mpr hil,Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp hwm).2,hrank⟩⟩
  simp only [outerBdry, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hwi,T.par w,hip,T.par_adj w (Finset.mem_filter.mp hwm).1 hwu⟩

lemma entryBoundary_budget {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (Δ m i : ℕ) (L : ℝ)
    (hr : ∀v,0 ≤ r v) (hL : 0 ≤ L) (him : i < m) (hm : m ≤ Mof Δ)
    (hentry : EntryEvent G Δ u L r) :
    ((entryBoundary T m i).card : ℝ) ≤
      32*c^(1+m-i)*(2*Sm r (T.prefix (am i)) m+L) := by
  classical
  have hact : ActiveAt G r (am m) (T.prefix (am i)) := by
    intro v hv
    exact (band_antitone him.le).trans (Finset.mem_filter.mp hv).2
  by_cases hne : (T.prefix (am i)).Nonempty
  · have hh := hentry m i him hm _ (prefix_connected G r u T (am i) hne) hact
    simpa [Kmi,KAB,hact,entryBoundary] using hh
  · have he : T.prefix (am i) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hc : 0 ≤ c := band_factor_gt_one.le.trans' (by norm_num)
    simp [entryBoundary,he,outerBdry,Sm,S]
    positivity

lemma entryBoundary_charge {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (Δ m i : ℕ) (L : ℝ)
    (hr : ∀v,0 ≤ r v) (hL : 0 ≤ L) (him : i < m) (hm : m ≤ Mof Δ)
    (hentry : EntryEvent G Δ u L r) :
    Sm r (entryBoundary T m i) m ≤
      32*c^2*(2*c^(3*(m-i))*Sm r (T.prefix (am i)) i+c^(2*(m-i))*L) := by
  classical
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  have hcap : Sm r (entryBoundary T m i) i ≤ c*(entryBoundary T m i).card := by
    apply charge_of_cap_bound
    intro v hv
    exact cap_rank_band r v i (Finset.mem_filter.mp hv).2.2
  have hb := entryBoundary_budget T Δ m i L hr hL him hm hentry
  rw [charge_scale r (T.prefix (am i)) him.le] at hb
  rw [charge_scale r (entryBoundary T m i) him.le]
  calc
    _ ≤ c^(m-i)*(c*(entryBoundary T m i).card) :=
      mul_le_mul_of_nonneg_left hcap (by positivity)
    _ ≤ c^(m-i)*(c*(32*c^(1+m-i)*(2*(c^(m-i)*Sm r (T.prefix (am i)) i)+L))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hc.le) (by positivity)
    _ = _ := by
      rw [show 1+m-i = (m-i)+1 by omega, pow_succ]
      simp only [mul_comm 3 (m-i), mul_comm 2 (m-i), pow_mul]
      ring

lemma bandFrontier_charge {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (Δ m : ℕ) (L : ℝ)
    (hr : ∀v,0 ≤ r v) (hL : 0 ≤ L) (hm0 : 1 ≤ m) (hm : m ≤ Mof Δ)
    (hentry : EntryEvent G Δ u L r) :
    Sm r (bandFrontier T m) m ≤ c*Sm r (T.prefix (am (m-1))) (m-1)+c^m+
      32*c^2*∑i∈Finset.range m,
        (2*c^(3*(m-i))*Sm r (T.prefix (am i)) i+c^(2*(m-i))*L) := by
  classical
  have hcover := charge_mono r hr _ _ (bandFrontier_cover T m hm0) m
  have hu := charge_union_le r hr {u}
    (T.prefix (am (m-1)) ∪ (Finset.range m).biUnion (entryBoundary T m)) m
  have hv := charge_union_le r hr (T.prefix (am (m-1)))
    ((Finset.range m).biUnion (entryBoundary T m)) m
  have hs := charge_biUnion_le r hr (Finset.range m) (entryBoundary T m) m
  have hb := Finset.sum_le_sum (fun i (hi : i ∈ Finset.range m) =>
    entryBoundary_charge T Δ m i L hr hL (Finset.mem_range.mp hi) hm hentry)
  rw [← Finset.mul_sum] at hb
  have hroot := charge_singleton_le r u m
  have hprev : Sm r (T.prefix (am (m-1))) m = c*Sm r (T.prefix (am (m-1))) (m-1) := by
    rw [charge_scale r _ (Nat.sub_le m 1), show m-(m-1)=1 by omega, pow_one]
  rw [hprev] at hv
  linarith

lemma prefix_charge_step {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {r : V → ℝ} {u : V}
    (T : AdmissibleTree G r u) (Δ m : ℕ) (L : ℝ)
    (hr : ∀v,0 ≤ r v) (hL : 0 ≤ L) (hm0 : 1 ≤ m) (hm : m ≤ Mof Δ)
    (hgrowth : GrowthEvent G Δ u L r) :
    Sm r (T.prefix (am m)) m ≤ (1+2*c)*Sm r (bandFrontier T m) m+c*L := by
  classical
  have hc : 0 ≤ c := (lt_trans (by norm_num) band_factor_gt_one).le
  by_cases hne : (T.prefix (am m)).Nonempty
  · have hg := hgrowth m hm0 hm _ (bandFrontier_connected T m hne) (bandFrontier_active T m)
    have hcard : ((T.prefix (am m) \ bandFrontier T m).card : ℝ) ≤
        ((Gammam G r m (bandFrontier T m)).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (band_remainder_subset T m))
    have hcap : Sm r (T.prefix (am m) \ bandFrontier T m) m ≤
        c*(T.prefix (am m) \ bandFrontier T m).card := by
      apply charge_of_cap_bound
      intro v hv
      exact (min_le_left _ _).trans ((band_remainder_rank T m v hv).le.trans
        (band_previous m hm0).le)
    have he : T.prefix (am m) = bandFrontier T m ∪ (T.prefix (am m) \ bandFrontier T m) := by
      exact (Finset.union_sdiff_of_subset Finset.inter_subset_left).symm
    have hu := charge_union_le r hr (bandFrontier T m) (T.prefix (am m) \ bandFrontier T m) m
    rw [← he] at hu
    have hh := mul_le_mul_of_nonneg_left (hcard.trans hg) hc
    nlinarith
  · have he := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he]
    simp only [Sm,S,Finset.sum_empty,mul_zero]
    have ha := charge_nonneg r hr (bandFrontier T m) m
    positivity
end P41PrefixGeometry
open P41PrefixGeometry

namespace P41PrefixRecurrence
open RGMISFast
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A rescaling of Appendix C allowing an absolute factor 6 in place of 3. -/
lemma prefix_rescaled_step (σ : ℕ → ℝ) (L : ℝ) (hL : 1 ≤ L)
    (hs : ∀i,0 ≤ σ i) (m : ℕ) (hm : 1 ≤ m)
    (hstep : σ m ≤ (1+2*c)*(c*σ (m-1)+c^m+
      32*c^2*∑i∈Finset.range m,(2*c^(3*(m-i))*σ i+c^(2*(m-i))*L))+c*L) :
    σ m/c^(3*m)+L ≤ 255*(∑i∈Finset.range m,(σ i/c^(3*i)+L))+10*L := by
  let p := fun i : ℕ => c^(3*i)
  let X := fun i : ℕ => σ i/p i+L
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  have hL0 : 0 ≤ L := by linarith
  have hp : ∀i,0 < p i := fun i => by dsimp [p]; positivity
  have hp1 : ∀i,1 ≤ p i := fun i => one_le_pow₀ band_factor_gt_one.le
  have hx : ∀i,0 ≤ X i := fun i => add_nonneg (div_nonneg (hs i) (hp i).le) hL0
  have he : ∀i,p i*X i = σ i+p i*L := by
    intro i; dsimp [X]; field_simp [(hp i).ne']
  have hmul : ∀ i, i ≤ m →c^(3*(m-i))*p i=p m := by
    intro i hi
    dsimp [p]
    rw [← pow_add]
    congr 1
    omega
  have hterm : ∀i∈Finset.range m, 2*c^(3*(m-i))*σ i+c^(2*(m-i))*L ≤ 2*p m*X i := by
    intro i hi
    have him : i ≤ m := (Finset.mem_range.mp hi).le
    have hpow : c^(2*(m-i)) ≤ p m := pow_le_pow_right₀ band_factor_gt_one.le (by omega)
    have hpowL := mul_le_mul_of_nonneg_right hpow hL0
    have hiEq := congrArg (fun z : ℝ => c^(3*(m-i))*z) (he i)
    have hiMul := hmul i him
    simp only [mul_add, ← mul_assoc, hiMul] at hiEq
    have hiL : 0 ≤ p m*L := mul_nonneg (hp m).le hL0
    nlinarith only [hiEq, hiMul, hpowL, hiL]
  have hsum : (∑i∈Finset.range m,(2*c^(3*(m-i))*σ i+c^(2*(m-i))*L)) ≤
      2*p m*∑i∈Finset.range m,X i := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum hterm
  have hprev : c*σ (m-1) ≤ p m*X (m-1) := by
    have hpow : c*p (m-1) ≤ p m := by
      dsimp [p]
      rw [← pow_succ']
      exact pow_le_pow_right₀ band_factor_gt_one.le (by omega)
    have hpX := mul_le_mul_of_nonneg_right hpow (hx (m-1))
    have hec := congrArg (fun z : ℝ => c*z) (he (m-1))
    have hpos : 0 ≤ c*p (m-1)*L := by positivity
    nlinarith only [hpX, hec, hpos]
  have hroot : c^m ≤ p m*L := by
    have hpow : c^m ≤ p m := pow_le_pow_right₀ band_factor_gt_one.le (by omega)
    have hmul := mul_le_mul_of_nonneg_left hL (hp m).le
    linarith
  have hcL : c*L ≤ p m*(c*L) := by
    have hh := mul_le_mul_of_nonneg_right (hp1 m) (show 0 ≤ c*L by positivity)
    simpa using hh
  have hXprev : X (m-1) ≤ ∑i∈Finset.range m,X i :=
    Finset.single_le_sum (fun i _ => hx i) (Finset.mem_range.mpr (by omega))
  have hXsum : 0 ≤ ∑i∈Finset.range m,X i := Finset.sum_nonneg (fun i _ => hx i)
  have hsumscaled := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 32*c^2 by positivity)
  have hinside : c*σ (m-1)+c^m+32*c^2*∑i∈Finset.range m,
      (2*c^(3*(m-i))*σ i+c^(2*(m-i))*L) ≤
      p m*(X (m-1)+L+64*c^2*∑i∈Finset.range m,X i) := by nlinarith only [hprev, hroot, hsumscaled]
  have hscaled := mul_le_mul_of_nonneg_left hinside (show 0 ≤ 1+2*c by positivity)
  have hprevmul := mul_le_mul_of_nonneg_left hXprev (show 0 ≤ (1+2*c)*p m by positivity)
  have hcoeff := mul_le_mul_of_nonneg_right recurrence_coefficient_bound
    (show 0 ≤ p m*(∑i∈Finset.range m,X i) by positivity)
  have hconst : (2+3*c)*L ≤ 10*L := by
    apply mul_le_mul_of_nonneg_right _ hL0
    have hh := band_factor_le_eleven_tenths
    linarith
  have hconstmul := mul_le_mul_of_nonneg_left hconst (hp m).le
  have hfinal : σ m+p m*L ≤ p m*(255*(∑i∈Finset.range m,X i)+10*L) := by
    nlinarith only [hstep, hscaled, hprevmul, hcoeff, hconstmul, hcL]
  change σ m/p m+L ≤ 255*(∑i∈Finset.range m,X i)+10*L
  apply (mul_le_mul_iff_of_pos_right (hp m)).mp
  have hediv : (σ m/p m+L)*p m = σ m+p m*L := by field_simp [(hp m).ne']
  rw [hediv]
  nlinarith only [hfinal]

lemma finite_prefix_bound (σ : ℕ → ℝ) (L : ℝ) (hL : 1 ≤ L) (M : ℕ)
    (hs : ∀i,0 ≤ σ i) (h0 : σ 0 ≤ 1+L)
    (hstep : ∀m,1 ≤ m → m ≤ M → σ m ≤ (1+2*c)*(c*σ (m-1)+c^m+
      32*c^2*∑i∈Finset.range m,(2*c^(3*(m-i))*σ i+c^(2*(m-i))*L))+c*L) :
    ∀m,m ≤ M → σ m ≤ 6*L*c^(3*m)*(256:ℝ)^m := by
  let X := fun i : ℕ => if i ≤ M then σ i/c^(3*i)+L else 0
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  have hL0 : 0 ≤ L := by linarith
  have hx : ∀i,0 ≤ X i := by
    intro i
    dsimp [X]
    split_ifs
    · exact add_nonneg (div_nonneg (hs i) (by positivity)) hL0
    · rfl
  have hx0 : X 0 ≤ 5*L := by
    dsimp [X]
    simp only [Nat.zero_le, if_true, mul_zero, pow_zero, div_one]
    linarith
  have hxstep : ∀m,X (m+1) ≤ 255*∑i∈Finset.range (m+1),X i+10*L := by
    intro m
    by_cases hm : m+1 ≤ M
    · have hh := prefix_rescaled_step σ L hL hs (m+1) (by omega) (hstep (m+1) (by omega) hm)
      have he : (∑i∈Finset.range (m+1),X i) =
          ∑i∈Finset.range (m+1),(σ i/c^(3*i)+L) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [X, show i ≤ M from (Finset.mem_range.mp hi).le.trans hm]
      rw [he]
      simpa only [X, if_pos hm] using hh
    · simp only [X, if_neg hm]
      have hsum : 0 ≤ ∑i∈Finset.range (m+1),X i := Finset.sum_nonneg (fun i _ => hx i)
      change 0 ≤ 255*∑i∈Finset.range (m+1),X i+10*L
      positivity
  have hb := appendix_c_recurrence X L hx0 hxstep
  intro m hm
  cases m with
  | zero => simp only [mul_zero,pow_zero,mul_one]; linarith
  | succ k =>
    have hh := hb k
    have hpow : 0 < c^(3*(k+1)) := by positivity
    have hxe : X (k+1)*c^(3*(k+1)) = σ (k+1)+L*c^(3*(k+1)) := by
      simp only [X,if_pos hm]
      field_simp
    have hh' := mul_le_mul_of_nonneg_right hh hpow.le
    have hnon : 0 ≤ L*c^(3*(k+1)) := by positivity
    have hpad : 1285*L*(256:ℝ)^k*c^(3*(k+1)) ≤
        6*L*c^(3*(k+1))*(256:ℝ)^(k+1) := by
      rw [pow_succ]
      have hpos : 0 ≤ L*(256:ℝ)^k*c^(3*(k+1)) := by positivity
      nlinarith
    rw [hxe] at hh'
    exact (by linarith : σ (k+1) ≤ 1285*L*(256:ℝ)^k*c^(3*(k+1))).trans hpad
end P41PrefixRecurrence
open P41PrefixRecurrence

namespace P41PrefixSharp
open RGMISFast
set_option autoImplicit false

lemma prefix_recurrence_sharp (X : ℕ → ℝ) (L : ℝ)
    (h0 : X 0 ≤ (5/2:ℝ)*L)
    (hstep : ∀ m : ℕ, X (m+1) ≤ 255 * ∑ i ∈ Finset.range (m+1), X i + 10*L) :
    ∀ m : ℕ, X (m+1) ≤ (1295/2:ℝ)*L*(256:ℝ)^m := by
  have hsum : ∀ m : ℕ, (∑ i ∈ Finset.range (m+1), X i) ≤
      (((1295/2:ℝ)*(256:ℝ)^m - 10)/255)*L := by
    intro m
    induction m with
    | zero => norm_num; exact h0
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep m
      have hmul := mul_le_mul_of_nonneg_left ih (by norm_num : (0:ℝ) ≤ 256)
      rw [pow_succ]
      nlinarith
  intro m
  have hs := hstep m
  have hb := hsum m
  nlinarith

lemma finite_prefix_bound_three (σ : ℕ → ℝ) (L : ℝ) (hL : 2 ≤ L) (M : ℕ)
    (hs : ∀i,0 ≤ σ i) (h0 : σ 0 ≤ 1+L)
    (hstep : ∀m,1 ≤ m → m ≤ M → σ m ≤ (1+2*c)*(c*σ (m-1)+c^m+
      32*c^2*∑i∈Finset.range m,(2*c^(3*(m-i))*σ i+c^(2*(m-i))*L))+c*L) :
    ∀m,m ≤ M → σ m ≤ 3*L*c^(3*m)*(256:ℝ)^m := by
  let X := fun i : ℕ => if i ≤ M then σ i/c^(3*i)+L else 0
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  have hL0 : 0 ≤ L := by linarith
  have hx : ∀i,0 ≤ X i := by
    intro i
    dsimp [X]
    split_ifs
    · exact add_nonneg (div_nonneg (hs i) (by positivity)) hL0
    · rfl
  have hx0 : X 0 ≤ (5/2:ℝ)*L := by
    dsimp [X]
    simp only [Nat.zero_le, if_true, mul_zero, pow_zero, div_one]
    linarith
  have hxstep : ∀m,X (m+1) ≤ 255*∑i∈Finset.range (m+1),X i+10*L := by
    intro m
    by_cases hm : m+1 ≤ M
    · have hh := prefix_rescaled_step σ L (by linarith) hs (m+1) (by omega) (hstep (m+1) (by omega) hm)
      have he : (∑i∈Finset.range (m+1),X i) =
          ∑i∈Finset.range (m+1),(σ i/c^(3*i)+L) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [X, show i ≤ M from (Finset.mem_range.mp hi).le.trans hm]
      rw [he]
      simpa only [X, if_pos hm] using hh
    · simp only [X, if_neg hm]
      have hsum : 0 ≤ ∑i∈Finset.range (m+1),X i := Finset.sum_nonneg (fun i _ => hx i)
      change 0 ≤ 255*∑i∈Finset.range (m+1),X i+10*L
      positivity
  have hb := prefix_recurrence_sharp X L hx0 hxstep
  intro m hm
  cases m with
  | zero => simp only [mul_zero,pow_zero,mul_one]; linarith
  | succ k =>
    have hh := hb k
    have hpow : 0 < c^(3*(k+1)) := by positivity
    have hxe : X (k+1)*c^(3*(k+1)) = σ (k+1)+L*c^(3*(k+1)) := by
      simp only [X,if_pos hm]
      field_simp
    have hh' := mul_le_mul_of_nonneg_right hh hpow.le
    have hnon : 0 ≤ L*c^(3*(k+1)) := by positivity
    have hpad : (1295/2:ℝ)*L*(256:ℝ)^k*c^(3*(k+1)) ≤
        3*L*c^(3*(k+1))*(256:ℝ)^(k+1) := by
      rw [pow_succ]
      have hpos : 0 ≤ L*(256:ℝ)^k*c^(3*(k+1)) := by positivity
      nlinarith
    rw [hxe] at hh'
    exact (by linarith : σ (k+1) ≤ (1295/2:ℝ)*L*(256:ℝ)^k*c^(3*(k+1))).trans hpad
end P41PrefixSharp
open P41PrefixSharp

set_option autoImplicit false
open RGMISFast

/-- Proposition 4.1 (Size of admissible trees; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.15, proof in App. C): conditioned on
`E_h`, every admissible tree `T` satisfies, for `0 ≤ m ≤ M`,
`S_m(T_{a_m}) ≤ 3L (a₀/a_m)^3 256^m` (14), and in particular
`|V(T_{a_M})| ≤ 3L (a₀/a_M)^3 256^M`.

**Formalization Note** `L = h + 8` with `h ≥ 0` (p.15); `E_h` is `GoodEvent G Δ u (h + 8)`;
`M = Mof Δ`. Ranks are distinct and nonnegative (standing assumption of §2), degrees are at most
`∆`, `∆ ≥ 2`. Both clauses are stated. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀ v, G.degree v ≤ Δ) (u : V) (h : ℝ)
    (hh : 0 ≤ h) (r : V → ℝ) (hinj : Function.Injective r) (hnn : ∀ v, 0 ≤ r v)
    (hE : GoodEvent G Δ u (h + 8) r) (T : AdmissibleTree G r u) :
    (∀ m : ℕ, m ≤ Mof Δ →
      Sm r (T.prefix (am m)) m ≤ 3 * (h + 8) * (a0 / am m) ^ 3 * 256 ^ m) ∧
    ((T.prefix (am (Mof Δ))).card : ℝ) ≤
      3 * (h + 8) * (a0 / am (Mof Δ)) ^ 3 * 256 ^ (Mof Δ)  := by
  have hc : 0 < c := lt_trans (by norm_num) band_factor_gt_one
  have ha : 0 < a0 := Real.exp_pos 2
  let L := h+8
  have hL : 2 ≤ L := by dsimp [L]; linarith
  have hgood : GoodEvent G Δ u L r := hE
  have hr : ∀v,0 ≤ r v := hnn
  have hstep : ∀m,1 ≤ m → m ≤ Mof Δ →
      Sm r (T.prefix (am m)) m ≤ (1+2*c)*
      (c*Sm r (T.prefix (am (m-1))) (m-1)+c^m+
       32*c^2*∑i∈Finset.range m,
         (2*c^(3*(m-i))*Sm r (T.prefix (am i)) i+c^(2*(m-i))*L))+c*L := by
    intro m hm0 hm
    have hh := prefix_charge_step T Δ m L hr (by linarith) hm0 hm hgood.2.1
    have hb := bandFrontier_charge T Δ m L hr (by linarith) hm0 hm hgood.1
    have hm' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1+2*c by positivity)
    linarith
  have hb := finite_prefix_bound_three (fun m => Sm r (T.prefix (am m)) m)
    L hL (Mof Δ) (fun m => charge_nonneg r hr _ m)
    (top_charge_bound T L hgood.2.2.1) hstep
  have hall : ∀m,m ≤ Mof Δ → Sm r (T.prefix (am m)) m ≤
      3*(h+8)*(a0/am m)^3*256^m := by
    intro m hm
    have he : a0/am m = c^m := by unfold am; field_simp
    rw [he, ← pow_mul, Nat.mul_comm m 3]
    exact hb m hm
  exact ⟨hall,(charge_active_card _ _ (prefix_active G r u T (am (Mof Δ)))).trans
    (hall (Mof Δ) le_rfl)⟩


