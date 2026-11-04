-- Prove2me | solution 1 for ReserveLP.ProLPR.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:20:47.968366+00:00
-- url     : https://prove2.me/submissions/7b404a5b-1a75-42e6-8e2d-6059e2332ac2

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

open ReserveLP.ProLPR Finset

/-- `Σ_{b∈U} c_b ∏_{b'∈U∖b} f_{b'}`. -/
noncomputable def rlpSS {ι : Type} [DecidableEq ι] (U : Finset ι) (f c : ι → ℝ) : ℝ :=
  ∑ b ∈ U, c b * ∏ b' ∈ U.erase b, f b'

theorem rlpSS_insert {ι : Type} [DecidableEq ι] (U : Finset ι) (f c : ι → ℝ) (b : ι)
    (hb : b ∉ U) : rlpSS (insert b U) f c = rlpSS U f c * f b + c b * ∏ b' ∈ U, f b' := by
  unfold rlpSS
  rw [sum_insert hb, erase_insert hb, sum_mul, add_comm]
  congr 1
  refine sum_congr rfl fun b' hb' => ?_
  have hne : b' ≠ b := fun h => hb (h ▸ hb')
  rw [erase_insert_of_ne (Ne.symm hne), prod_insert (fun h => hb (mem_of_mem_erase h))]
  ring

theorem rlpSS_nonneg {ι : Type} [DecidableEq ι] (U : Finset ι) (f c : ι → ℝ)
    (hf : ∀ b ∈ U, 0 ≤ f b) (hc : ∀ b ∈ U, 0 ≤ c b) : 0 ≤ rlpSS U f c := by
  unfold rlpSS
  exact sum_nonneg fun b hb => mul_nonneg (hc b hb)
    (prod_nonneg fun b' hb' => hf b' (mem_of_mem_erase hb'))

/-- `∏ f + Σ c ∏ f ≤ 1` when `f, c ≥ 0`, `f + c ≤ 1`. -/
theorem rlp_T_le_one {ι : Type} [DecidableEq ι] (U : Finset ι) (f c : ι → ℝ)
    (hf : ∀ b ∈ U, 0 ≤ f b) (hc : ∀ b ∈ U, 0 ≤ c b) (hfc : ∀ b ∈ U, f b + c b ≤ 1) :
    ∏ b ∈ U, f b ≤ 1 ∧ ∏ b ∈ U, f b + rlpSS U f c ≤ 1 := by
  induction U using Finset.induction_on with
  | empty => simp [rlpSS]
  | insert b U hb ih =>
    have hf' : ∀ b ∈ U, 0 ≤ f b := fun b' h => hf b' (mem_insert_of_mem h)
    have hc' : ∀ b ∈ U, 0 ≤ c b := fun b' h => hc b' (mem_insert_of_mem h)
    obtain ⟨h1, h2⟩ := ih hf' hc' (fun b' h => hfc b' (mem_insert_of_mem h))
    have hP : 0 ≤ ∏ b ∈ U, f b := prod_nonneg hf'
    have hS := rlpSS_nonneg U f c hf' hc'
    have hfb := hf b (mem_insert_self _ _)
    have hcb := hc b (mem_insert_self _ _)
    have hfcb := hfc b (mem_insert_self _ _)
    rw [prod_insert hb, rlpSS_insert U f c b hb]
    constructor
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left h2 hfb, mul_le_mul_of_nonneg_left h1 hcb]

/-- Monotonicity of `∏ f + Σ c ∏ f` (the probability of the complement event). -/
theorem rlp_L_mono {ι : Type} [DecidableEq ι] (U : Finset ι) (fx cx fy cy : ι → ℝ)
    (hfy : ∀ b ∈ U, 0 ≤ fy b) (hf : ∀ b ∈ U, fy b ≤ fx b) (hcx : ∀ b ∈ U, 0 ≤ cx b)
    (hcy : ∀ b ∈ U, 0 ≤ cy b)
    (hs : ∀ b ∈ U, fy b + cy b ≤ fx b + cx b) :
    ∏ b ∈ U, fy b ≤ ∏ b ∈ U, fx b ∧
      ∏ b ∈ U, fy b + rlpSS U fy cy ≤ ∏ b ∈ U, fx b + rlpSS U fx cx := by
  induction U using Finset.induction_on with
  | empty => simp [rlpSS]
  | insert b U hb ih =>
    have m : ∀ {P : ι → Prop}, (∀ b' ∈ insert b U, P b') → ∀ b' ∈ U, P b' :=
      fun h b' hb' => h b' (mem_insert_of_mem hb')
    obtain ⟨h1, h2⟩ := ih (m hfy) (m hf) (m hcx) (m hcy) (m hs)
    have hPy : 0 ≤ ∏ b ∈ U, fy b := prod_nonneg (m hfy)
    have hfx' : ∀ b' ∈ U, 0 ≤ fx b' := fun b' h => (m hfy b' h).trans (m hf b' h)
    have hSx := rlpSS_nonneg U fx cx hfx' (m hcx)
    have hSy := rlpSS_nonneg U fy cy (m hfy) (m hcy)
    have e1 := hfy b (mem_insert_self _ _)
    have e2 := hf b (mem_insert_self _ _)
    have e3 := hcx b (mem_insert_self _ _)
    have e4 := hcy b (mem_insert_self _ _)
    have e5 := hs b (mem_insert_self _ _)
    rw [prod_insert hb, prod_insert hb, rlpSS_insert U fy cy b hb, rlpSS_insert U fx cx b hb]
    constructor
    · exact mul_le_mul e2 h1 hPy (e1.trans e2)
    · -- (Py+Sy) fy + cy Py ≤ (Px+Sx) fx + cx Px
      have k1 : (∏ b ∈ U, fy b + rlpSS U fy cy) * fy b ≤
          (∏ b ∈ U, fx b + rlpSS U fx cx) * fy b := mul_le_mul_of_nonneg_right h2 e1
      have k2 : (∏ b ∈ U, fy b) * (cy b - cx b + fy b - fx b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hPy (by linarith)
      have k3 : (∏ b ∈ U, fy b) * (fx b - fy b) ≤
          (∏ b ∈ U, fx b + rlpSS U fx cx) * (fx b - fy b) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have k4 : (∏ b ∈ U, fy b) * cx b ≤ (∏ b ∈ U, fx b) * cx b :=
        mul_le_mul_of_nonneg_right h1 e3
      nlinarith

/-- Lemma 5.4. -/
theorem rlp_lemma54 {ι : Type} [DecidableEq ι] (U : Finset ι) (a c : ι → ℝ)
    (ha : ∀ b ∈ U, 0 ≤ a b) (hc : ∀ b ∈ U, 0 ≤ c b) (hac : ∀ b ∈ U, a b + c b ≤ 1) :
    ∏ b ∈ U, (1 - a b - c b) ≤ (∏ b ∈ U, (1 - a b)) * ∏ b ∈ U, (1 - c b) ∧
    ∏ b ∈ U, (1 - a b - c b) + rlpSS U (fun b => 1 - a b - c b) c ≤
      (∏ b ∈ U, (1 - a b)) * (∏ b ∈ U, (1 - c b) + rlpSS U (fun b => 1 - c b) c) := by
  induction U using Finset.induction_on with
  | empty => simp [rlpSS]
  | insert b U hb ih =>
    have m : ∀ {P : ι → Prop}, (∀ b' ∈ insert b U, P b') → ∀ b' ∈ U, P b' :=
      fun h b' hb' => h b' (mem_insert_of_mem hb')
    obtain ⟨h1, h2⟩ := ih (m ha) (m hc) (m hac)
    have hP : 0 ≤ ∏ b ∈ U, (1 - a b - c b) :=
      prod_nonneg fun b' h => by linarith [m hac b' h]
    have hA : 0 ≤ ∏ b ∈ U, (1 - a b) := prod_nonneg fun b' h => by linarith [m hac b' h, m hc b' h]
    have hP2 : 0 ≤ ∏ b ∈ U, (1 - c b) := prod_nonneg fun b' h => by linarith [m hac b' h, m ha b' h]
    have hS2 := rlpSS_nonneg U (fun b => 1 - c b) c
      (fun b' h => by linarith [m hac b' h, m ha b' h]) (m hc)
    have e1 := ha b (mem_insert_self _ _)
    have e2 := hc b (mem_insert_self _ _)
    have e3 := hac b (mem_insert_self _ _)
    rw [prod_insert hb, prod_insert hb, prod_insert hb,
      rlpSS_insert U _ c b hb, rlpSS_insert U _ c b hb]
    set P := ∏ b ∈ U, (1 - a b - c b)
    set A := ∏ b ∈ U, (1 - a b)
    set P2 := ∏ b ∈ U, (1 - c b)
    set S := rlpSS U (fun b => 1 - a b - c b) c
    set S2 := rlpSS U (fun b => 1 - c b) c
    have hf : 0 ≤ 1 - a b - c b := by linarith
    have hAP2 : 0 ≤ A * P2 := mul_nonneg hA hP2
    constructor
    · have : (1 - a b - c b) ≤ (1 - a b) * (1 - c b) := by nlinarith
      calc (1 - a b - c b) * P ≤ (1 - a b - c b) * (A * P2) := mul_le_mul_of_nonneg_left h1 hf
        _ ≤ (1 - a b) * (1 - c b) * (A * P2) := mul_le_mul_of_nonneg_right this hAP2
        _ = (1 - a b) * A * ((1 - c b) * P2) := by ring
    · have k1 : (P + S) * (1 - a b - c b) ≤ A * (P2 + S2) * (1 - a b - c b) :=
        mul_le_mul_of_nonneg_right h2 hf
      have k2 : c b * P ≤ c b * (A * P2) := mul_le_mul_of_nonneg_left h1 e2
      have k3 : 0 ≤ A * (a b * c b) * S2 := mul_nonneg (mul_nonneg hA (mul_nonneg e1 e2)) hS2
      have goal_eq : (1 - a b - c b) * P + (S * (1 - a b - c b) + c b * P) =
          (P + S) * (1 - a b - c b) + c b * P := by ring
      rw [goal_eq]
      nlinarith

theorem rlp_prod_le_exp {ι : Type} (U : Finset ι) (a : ι → ℝ) (ha : ∀ b ∈ U, a b ≤ 1) :
    ∏ b ∈ U, (1 - a b) ≤ Real.exp (-∑ b ∈ U, a b) := by
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod
  · intro b hb; linarith [ha b hb]
  · intro b _; linarith [Real.add_one_le_exp (-a b)]

theorem rlp_scalar (σ θ A T : ℝ) (hσ : 0 ≤ σ) (hσθ : σ + θ ≤ 1) (hA : A ≤ Real.exp (-σ))
    (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    σ + θ - 1 + A * T ≤ Real.exp (θ - 1) * T := by
  have hAT : A * T ≤ Real.exp (-σ) * T := mul_le_mul_of_nonneg_right hA hT0
  set d := 1 - θ - σ with hd
  have hd0 : 0 ≤ d := by linarith
  have he : Real.exp (θ - 1) = Real.exp (-σ) * Real.exp (-d) := by
    rw [← Real.exp_add]; congr 1; linarith
  have h1 : 1 - d ≤ Real.exp (-d) := by linarith [Real.add_one_le_exp (-d)]
  have h2 : Real.exp (-σ) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have h3 : 0 < Real.exp (-σ) := Real.exp_pos _
  have h4 : Real.exp (-d) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  -- exp(-σ) T - exp(-σ) exp(-d) T = exp(-σ) T (1 - exp(-d)) ≤ 1 * 1 * d
  have h5 : Real.exp (-σ) * T * (1 - Real.exp (-d)) ≤ d := by
    have : Real.exp (-σ) * T ≤ 1 := by nlinarith
    calc Real.exp (-σ) * T * (1 - Real.exp (-d)) ≤ 1 * (1 - Real.exp (-d)) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ ≤ d := by linarith
  rw [he]
  nlinarith

theorem rlp_Fobj_le (n : ℕ) (θ : ℝ) (x : Fin n → ℝ) (hx : OPTFeasible n θ x) (hθ1 : θ ≤ 1) :
    Fobj x θ ≤ Real.exp (θ - 1) := by
  obtain ⟨h0, _, hle⟩ := hx
  have := (rlp_T_le_one (univ : Finset (Fin n)) (fun i => 1 - x i) x
    (fun i _ => by linarith [hle i]) (fun i _ => h0 i) (fun i _ => by linarith)).2
  unfold Fobj
  have hS : ∑ i, x i * ∏ j ∈ univ.erase i, (1 - x j) = rlpSS univ (fun i => 1 - x i) x := rfl
  rw [hS]
  calc Real.exp (θ - 1) * (∏ i, (1 - x i) + rlpSS univ (fun i => 1 - x i) x)
      ≤ Real.exp (θ - 1) * 1 := mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
    _ = Real.exp (θ - 1) := mul_one _

theorem rlp_le_cOPT (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Icc (0:ℝ) 1) (x : Fin n → ℝ)
    (hx : OPTFeasible n θ x) : Fobj x θ ≤ cOPT n := by
  have hOPT : Fobj x θ ≤ OPT n θ := by
    unfold OPT
    apply le_csSup
    · refine ⟨Real.exp (θ - 1), ?_⟩
      rintro v ⟨y, hy, rfl⟩
      exact rlp_Fobj_le n θ y hy hθ.2
    · exact ⟨x, hx, rfl⟩
  refine hOPT.trans ?_
  unfold cOPT
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro v ⟨θ', hθ', rfl⟩
    unfold OPT
    apply Real.sSup_le
    · rintro v ⟨y, hy, rfl⟩
      refine (rlp_Fobj_le n θ' y hy hθ'.2).trans ?_
      rw [Real.exp_le_one_iff]; linarith [hθ'.2]
    · norm_num
  · exact Set.mem_image_of_mem _ hθ

section
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]

theorem rlp53_mem_valid (D : DataSet A B) (a : A) (p : Profile B) :
    p ∈ validProfiles D a ↔ (p.2.2.1 ∈ reserves D ∧ p.2.2.2 ∈ reserves D) ∧ p.1 ≠ p.2.1 ∧
      D.bid a p.2.1 ≤ D.bid a p.1 ∧ p.2.2.1 ≤ D.bid a p.1 ∧ p.2.2.2 ≤ D.bid a p.2.1 := by
  simp [validProfiles, mem_filter, mem_product]

theorem rlp53_rev_ge (D : DataSet A B) (a : A) (ρ : B → ℝ) (t : ℝ)
    (h : (∃ b ∈ cleared D a ρ, t ≤ ρ b) ∨
      (∃ b b', b ≠ b' ∧ b ∈ cleared D a ρ ∧ b' ∈ cleared D a ρ ∧ t ≤ D.bid a b ∧ t ≤ D.bid a b')) :
    t ≤ revA D a ρ := by
  have hne : (cleared D a ρ).Nonempty := by
    rcases h with ⟨b, hb, _⟩ | ⟨b, _, _, hb, _⟩
    · exact ⟨b, hb⟩
    · exact ⟨b, hb⟩
  obtain ⟨w, hw, hwmax⟩ := exists_max_image (cleared D a ρ) (D.bid a) hne
  have hwt : w ∈ topBidders D a ρ := mem_filter.mpr ⟨hw, hwmax⟩
  have hrev : max (ρ w) (otherMax D a ρ w) ≤ revA D a ρ := by
    unfold revA; rw [dif_pos ⟨w, hwt⟩]
    exact le_sup' (fun w => max (ρ w) (otherMax D a ρ w)) hwt
  have hom : ∀ b ∈ cleared D a ρ, b ≠ w → D.bid a b ≤ otherMax D a ρ w := by
    intro b hb hbw
    unfold otherMax
    exact le_max' _ _ (mem_insert_of_mem (mem_image_of_mem _ (mem_erase.mpr ⟨hbw, hb⟩)))
  rcases h with ⟨b, hb, htb⟩ | ⟨b, b', hbb', hb, hb', htb, htb'⟩
  · by_cases hbw : b = w
    · subst hbw; exact htb.trans ((le_max_left _ _).trans hrev)
    · have hcl : ρ b ≤ D.bid a b := (mem_filter.mp hb).2
      exact htb.trans (hcl.trans ((hom b hb hbw).trans ((le_max_right _ _).trans hrev)))
  · by_cases hbw : b = w
    · have hb'w : b' ≠ w := fun h => hbb' (hbw.trans h.symm)
      exact htb'.trans ((hom b' hb' hb'w).trans ((le_max_right _ _).trans hrev))
    · exact htb.trans ((hom b hb hbw).trans ((le_max_right _ _).trans hrev))

theorem rlp53_rect (D : DataSet A B) (q : B → ℝ → ℝ) (g : B → ℝ → ℝ) :
    ∑ ρ ∈ roundings D, roundProb q ρ * ∏ b, g b (ρ b) =
      ∏ b, ∑ x ∈ reserves D, q b x * g b x := by
  unfold roundings roundProb
  rw [Finset.prod_univ_sum]
  refine sum_congr rfl fun ρ _ => ?_
  rw [prod_mul_distrib]

theorem rlp53_massQ (D : DataSet A B) (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (a : A)
    (hs0 : ∀ p ∈ validProfiles D a, 0 ≤ s a p)
    (hQ : ∀ b, ∀ r ∈ reserves D, ∑ p ∈ Qset D a b r, s a p ≤ q b r)
    (b : B) (P : Profile B → Prop) [DecidablePred P] (h : Profile B → ℝ) (R' : Finset ℝ)
    (hR' : R' ⊆ reserves D)
    (hP : ∀ p ∈ validProfiles D a, P p → h p ∈ R' ∧ p ∈ Qset D a b (h p)) :
    ∑ p ∈ validProfiles D a, s a p * (if P p then 1 else 0) ≤ ∑ x ∈ R', q b x := by
  have e : ∑ p ∈ validProfiles D a, s a p * (if P p then 1 else 0) =
      ∑ p ∈ (validProfiles D a).filter P, s a p := by
    rw [sum_filter]; refine sum_congr rfl fun p _ => ?_; split_ifs <;> simp
  rw [e]
  have hmaps : ∀ p ∈ (validProfiles D a).filter P, h p ∈ R' := by
    intro p hp; obtain ⟨hv, hPp⟩ := mem_filter.mp hp; exact (hP p hv hPp).1
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_le_sum
  intro x hx
  refine le_trans ?_ (hQ b x (hR' hx))
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp1, hpx⟩ := mem_filter.mp hp
    obtain ⟨hv, hPp⟩ := mem_filter.mp hp1
    have := (hP p hv hPp).2
    rwa [hpx] at this
  · intro p hp _
    exact hs0 p (mem_filter.mp hp).1

end

section
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]

theorem rlp53_prob_lt (D : DataSet A B) (q : B → ℝ → ℝ) (a : A) (t : ℝ)
    (hq0 : ∀ b, ∀ r ∈ reserves D, 0 ≤ q b r) (hq1 : ∀ b, ∑ r ∈ reserves D, q b r = 1) :
    ∑ ρ ∈ roundings D, roundProb q ρ * (if revA D a ρ < t then 1 else 0) ≤
      ∏ b ∈ univ.filter (fun b => t ≤ D.bid a b),
          (∑ x ∈ (reserves D).filter (fun x => D.bid a b < x), q b x) +
        rlpSS (univ.filter (fun b => t ≤ D.bid a b))
          (fun b => ∑ x ∈ (reserves D).filter (fun x => D.bid a b < x), q b x)
          (fun b => ∑ x ∈ (reserves D).filter (fun x => x < t), q b x) := by
  classical
  set U := univ.filter (fun b => t ≤ D.bid a b) with hU
  let y2 : B → ℝ := fun b => ∑ x ∈ (reserves D).filter (fun x => x < t), q b x
  let y3 : B → ℝ := fun b => ∑ x ∈ (reserves D).filter (fun x => D.bid a b < x), q b x
  let g0 : B → ℝ → ℝ := fun b x =>
    if t ≤ D.bid a b then (if D.bid a b < x then 1 else 0) else 1
  let gk : B → B → ℝ → ℝ := fun k b x =>
    if b = k then (if x < t then 1 else 0) else
      (if t ≤ D.bid a b then (if D.bid a b < x then 1 else 0) else 1)
  have g0nn : ∀ b x, 0 ≤ g0 b x := by intro b x; simp only [g0]; split_ifs <;> norm_num
  have gknn : ∀ k b x, 0 ≤ gk k b x := by intro k b x; simp only [gk]; split_ifs <;> norm_num
  -- pointwise bound
  have hpt : ∀ ρ : B → ℝ, (if revA D a ρ < t then (1:ℝ) else 0) ≤
      ∏ b, g0 b (ρ b) + ∑ k ∈ U, ∏ b, gk k b (ρ b) := by
    intro ρ
    have hnn : 0 ≤ ∏ b, g0 b (ρ b) + ∑ k ∈ U, ∏ b, gk k b (ρ b) :=
      add_nonneg (prod_nonneg fun b _ => g0nn b _)
        (sum_nonneg fun k _ => prod_nonneg fun b _ => gknn k b _)
    split_ifs with hlt
    swap; · exact hnn
    -- consequences of revenue < t
    have hi : ∀ b, t ≤ D.bid a b → ρ b < t ∨ D.bid a b < ρ b := by
      intro b hb
      by_contra hcon
      push_neg at hcon
      have : t ≤ revA D a ρ := rlp53_rev_ge D a ρ t
        (Or.inl ⟨b, mem_filter.mpr ⟨mem_univ _, hcon.2⟩, hcon.1⟩)
      linarith
    have hii : ∀ b b', t ≤ D.bid a b → t ≤ D.bid a b' → ρ b < t → ρ b' < t → b = b' := by
      intro b b' hb hb' hρb hρb'
      by_contra hne
      have : t ≤ revA D a ρ := rlp53_rev_ge D a ρ t (Or.inr ⟨b, b', hne,
        mem_filter.mpr ⟨mem_univ _, by linarith⟩, mem_filter.mpr ⟨mem_univ _, by linarith⟩, hb, hb'⟩)
      linarith
    by_cases hk : ∃ k ∈ U, ρ k < t
    · obtain ⟨k, hkU, hkt⟩ := hk
      have hkb : t ≤ D.bid a k := (mem_filter.mp hkU).2
      have hprod : ∏ b, gk k b (ρ b) = 1 := by
        apply prod_eq_one
        intro b _
        simp only [gk]
        by_cases hbk : b = k
        · simp [hbk, hkt]
        · rw [if_neg hbk]
          by_cases hb : t ≤ D.bid a b
          · rw [if_pos hb]
            rcases hi b hb with h | h
            · exact absurd (hii b k hb hkb h hkt) hbk
            · simp [h]
          · rw [if_neg hb]
      have : (1:ℝ) ≤ ∑ k ∈ U, ∏ b, gk k b (ρ b) := by
        rw [← hprod]
        exact single_le_sum (f := fun k => ∏ b, gk k b (ρ b))
          (fun k _ => prod_nonneg fun b _ => gknn k b _) hkU
      linarith [prod_nonneg (s := (univ : Finset B)) fun b _ => g0nn b (ρ b)]
    · push_neg at hk
      have hprod : ∏ b, g0 b (ρ b) = 1 := by
        apply prod_eq_one
        intro b _
        simp only [g0]
        by_cases hb : t ≤ D.bid a b
        · rw [if_pos hb]
          rcases hi b hb with h | h
          · exact absurd h (not_lt.mpr (hk b (mem_filter.mpr ⟨mem_univ _, hb⟩)))
          · simp [h]
        · rw [if_neg hb]
      linarith [sum_nonneg (s := U) fun k _ => prod_nonneg (s := (univ : Finset B))
        fun b _ => gknn k b (ρ b)]
  have hπ0 : ∀ ρ ∈ roundings D, 0 ≤ roundProb q ρ := by
    intro ρ hρ
    exact prod_nonneg fun b _ => hq0 b _ (Fintype.mem_piFinset.mp hρ b)
  calc ∑ ρ ∈ roundings D, roundProb q ρ * (if revA D a ρ < t then 1 else 0)
      ≤ ∑ ρ ∈ roundings D, roundProb q ρ * (∏ b, g0 b (ρ b) + ∑ k ∈ U, ∏ b, gk k b (ρ b)) :=
        sum_le_sum fun ρ hρ => mul_le_mul_of_nonneg_left (hpt ρ) (hπ0 ρ hρ)
    _ = ∑ ρ ∈ roundings D, roundProb q ρ * ∏ b, g0 b (ρ b) +
          ∑ k ∈ U, ∑ ρ ∈ roundings D, roundProb q ρ * ∏ b, gk k b (ρ b) := by
        simp only [mul_add, sum_add_distrib, mul_sum]
        rw [sum_comm]
    _ = ∏ b, ∑ x ∈ reserves D, q b x * g0 b x +
          ∑ k ∈ U, ∏ b, ∑ x ∈ reserves D, q b x * gk k b x := by
        rw [rlp53_rect]
        refine congrArg _ (sum_congr rfl fun k _ => rlp53_rect D q (gk k))
    _ = ∏ b ∈ U, y3 b + rlpSS U y3 y2 := by
        have hy3 : ∀ b, t ≤ D.bid a b → ∑ x ∈ reserves D, q b x * (if D.bid a b < x then 1 else 0)
            = y3 b := by
          intro b _; simp only [y3, sum_filter, mul_ite, mul_one, mul_zero]
        have hq1' : ∀ b, ∑ x ∈ reserves D, q b x * (1:ℝ) = ∑ x ∈ reserves D, q b x := by
          intro b; simp
        have h0 : ∀ b, ∑ x ∈ reserves D, q b x * g0 b x =
            if t ≤ D.bid a b then y3 b else ∑ x ∈ reserves D, q b x := by
          intro b
          by_cases hb : t ≤ D.bid a b
          · simp only [g0, if_pos hb]; exact hy3 b hb
          · simp only [g0, if_neg hb, mul_one]
        have hk : ∀ k ∈ U, ∀ b, ∑ x ∈ reserves D, q b x * gk k b x =
            if b = k then y2 k else (if t ≤ D.bid a b then y3 b else 1) := by
          intro k _ b
          by_cases hbk : b = k
          · subst hbk; simp only [gk, if_true, y2, sum_filter, mul_ite, mul_one, mul_zero]
          · by_cases hb : t ≤ D.bid a b
            · simp only [gk, if_neg hbk, if_pos hb]; exact hy3 b hb
            · simp only [gk, if_neg hbk, if_neg hb, mul_one, hq1 b]
        have h0' : ∀ b, ∑ x ∈ reserves D, q b x * g0 b x = if t ≤ D.bid a b then y3 b else 1 := by
          intro b; rw [h0 b, hq1 b]
        simp only [h0']
        rw [← prod_filter]
        congr 1
        unfold rlpSS
        refine sum_congr rfl fun k hkU => ?_
        simp only [hk k hkU]
        rw [← mul_prod_erase univ _ (mem_univ k), if_pos rfl]
        congr 1
        rw [prod_congr rfl (fun b hb => if_neg (ne_of_mem_erase hb)), ← prod_filter, hU,
          filter_erase]
end

theorem solution {A B : Type} [Fintype A] [Fintype B] [DecidableEq B] (D : DataSet A B)
    (s : A → Profile B → ℝ) (q : B → ℝ → ℝ) (hopt : LPOptimal D s q) :
    ∀ a : A, ∀ t : ℝ, t ≤ secondBid D a →
      profileMassGe D s a t - probRevGe D q a t ≤ cOPT (Fintype.card B) := by
  classical
  intro a t _
  obtain ⟨⟨hs0, hs1, hQ, hq1, hq0⟩, _⟩ := hopt
  have hs0' : ∀ p ∈ validProfiles D a, 0 ≤ s a p := hs0 a
  set V := validProfiles D a with hV
  set U := univ.filter (fun b => t ≤ D.bid a b) with hU
  let gsel : Profile B → B := fun p => if t ≤ p.2.2.1 then p.1 else p.2.1
  let C1 : Profile B → Prop := fun p => t ≤ p.2.2.1 ∨ (p.2.2.1 < t ∧ t ≤ p.2.2.2)
  let C2 : Profile B → Prop := fun p => p.2.2.1 < t ∧ p.2.2.2 < t ∧ t ≤ D.bid a p.2.1
  let hsel : B → Profile B → ℝ := fun b p => if p.1 = b then p.2.2.1 else p.2.2.2
  let x1 : B → ℝ := fun b => ∑ p ∈ V, s a p * (if gsel p = b ∧ C1 p then 1 else 0)
  let x2 : B → ℝ := fun b => ∑ p ∈ V, s a p * (if (p.1 = b ∨ p.2.1 = b) ∧ C2 p then 1 else 0)
  let θ : ℝ := ∑ p ∈ V, s a p * (if C2 p then 1 else 0)
  let y1 : B → ℝ := fun b => ∑ x ∈ (reserves D).filter (fun x => t ≤ x ∧ x ≤ D.bid a b), q b x
  let y2 : B → ℝ := fun b => ∑ x ∈ (reserves D).filter (fun x => x < t), q b x
  let y3 : B → ℝ := fun b => ∑ x ∈ (reserves D).filter (fun x => D.bid a b < x), q b x
  have ind_nn : ∀ (P : Prop) [Decidable P], (0:ℝ) ≤ if P then 1 else 0 := by
    intro P _; split_ifs <;> norm_num
  -- Step A: the profile mass splits as Σ x1 + θ
  have hmass : profileMassGe D s a t = ∑ b ∈ U, x1 b + θ := by
    have hper : ∀ p ∈ V, (if t ≤ revProfile D a p then (1:ℝ) else 0) =
        (∑ b ∈ U, if gsel p = b ∧ C1 p then (1:ℝ) else 0) + (if C2 p then 1 else 0) := by
      intro p hp
      obtain ⟨_, hne, h12, hr1, hr2⟩ := (rlp53_mem_valid D a p).mp hp
      have hsum : (∑ b ∈ U, if gsel p = b ∧ C1 p then (1:ℝ) else 0) =
          if gsel p ∈ U ∧ C1 p then 1 else 0 := by
        simp only [ite_and]
        rw [sum_ite_eq]
      rw [hsum]
      simp only [revProfile, gsel, C1, C2, hU, mem_filter, mem_univ, true_and]
      by_cases ht1 : t ≤ p.2.2.1
      · have : ¬ p.2.2.1 < t := not_lt.mpr ht1
        simp [ht1, this, le_max_of_le_right ht1, ht1.trans hr1]
      · push_neg at ht1
        by_cases ht2 : t ≤ p.2.2.2
        · have hb2 : t ≤ D.bid a p.2.1 := ht2.trans hr2
          have : ¬ p.2.2.2 < t := not_lt.mpr ht2
          simp [not_le.mpr ht1, ht1, ht2, this, hb2, le_max_of_le_left hb2]
        · push_neg at ht2
          by_cases hb2 : t ≤ D.bid a p.2.1
          · simp [not_le.mpr ht1, ht1, ht2, hb2, not_le.mpr ht2, le_max_of_le_left hb2]
          · have hmx : ¬ t ≤ max (D.bid a p.2.1) p.2.2.1 := by
              rw [le_max_iff]; push_neg; exact ⟨lt_of_not_ge hb2, ht1⟩
            simp [not_le.mpr ht1, ht1, ht2, hb2, not_le.mpr ht2, hmx]
    unfold profileMassGe
    rw [← hV, sum_filter]
    have e1 : ∀ p ∈ V, (if t ≤ revProfile D a p then s a p else 0) =
        s a p * (if t ≤ revProfile D a p then (1:ℝ) else 0) := by
      intro p _; split_ifs <;> simp
    rw [sum_congr rfl e1, sum_congr rfl (fun p hp => by rw [hper p hp])]
    simp only [x1, θ, mul_add, sum_add_distrib, mul_sum]
    rw [sum_comm]
  -- Step B: Σ x2 = 2θ
  have hx2sum : ∑ b ∈ U, x2 b = 2 * θ := by
    simp only [x2, θ]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun p hp => ?_
    obtain ⟨_, hne, h12, _, _⟩ := (rlp53_mem_valid D a p).mp hp
    rw [← mul_sum]
    by_cases hc : C2 p
    · have hb2 : t ≤ D.bid a p.2.1 := hc.2.2
      have hfil : U.filter (fun b => p.1 = b ∨ p.2.1 = b) = {p.1, p.2.1} := by
        ext b
        simp only [hU, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        constructor
        · rintro ⟨_, h | h⟩ <;> [left; right] <;> exact h.symm
        · rintro (h | h) <;> subst h
          · exact ⟨hb2.trans h12, Or.inl rfl⟩
          · exact ⟨hb2, Or.inr rfl⟩
      have : (∑ b ∈ U, if (p.1 = b ∨ p.2.1 = b) ∧ C2 p then (1:ℝ) else 0) = 2 := by
        simp only [hc, and_true]
        rw [sum_boole, hfil, card_pair hne]; norm_num
      rw [this, if_pos hc]; ring
    · simp [hc]
  -- Step C: bounds on x
  have hx1y1 : ∀ b ∈ U, x1 b ≤ y1 b := by
    intro b hbU
    apply rlp53_massQ D s q a hs0' (hQ a) b _ (hsel b) _ (filter_subset _ _)
    intro p hp ⟨hg, hC⟩
    obtain ⟨⟨hr1R, hr2R⟩, hne, h12, hr1, hr2⟩ := (rlp53_mem_valid D a p).mp hp
    simp only [gsel] at hg
    simp only [C1] at hC
    by_cases ht1 : t ≤ p.2.2.1
    · rw [if_pos ht1] at hg
      subst hg
      refine ⟨?_, ?_⟩
      · simp only [hsel, if_true]; exact mem_filter.mpr ⟨hr1R, ht1, hr1⟩
      · simp [hsel, Qset, hp]
    · rw [if_neg ht1] at hg
      subst hg
      have ht2 : t ≤ p.2.2.2 := hC.elim (fun h => absurd h ht1) (fun h => h.2)
      simp only [hsel, if_neg hne]
      refine ⟨mem_filter.mpr ⟨hr2R, ht2, hr2⟩, ?_⟩
      exact mem_filter.mpr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
  have hx2y2 : ∀ b ∈ U, x2 b ≤ y2 b := by
    intro b hbU
    apply rlp53_massQ D s q a hs0' (hQ a) b _ (hsel b) _ (filter_subset _ _)
    intro p hp ⟨hb, hC⟩
    obtain ⟨⟨hr1R, hr2R⟩, hne, h12, hr1, hr2⟩ := (rlp53_mem_valid D a p).mp hp
    by_cases h1 : p.1 = b
    · simp only [hsel, if_pos h1]
      refine ⟨mem_filter.mpr ⟨hr1R, hC.1⟩, ?_⟩
      exact mem_filter.mpr ⟨hp, Or.inr ⟨h1, rfl⟩⟩
    · have h2 : p.2.1 = b := hb.resolve_left h1
      simp only [hsel, if_neg h1]
      refine ⟨mem_filter.mpr ⟨hr2R, hC.2.1⟩, ?_⟩
      exact mem_filter.mpr ⟨hp, Or.inl ⟨h2, rfl⟩⟩
  have hx1nn : ∀ b, 0 ≤ x1 b := fun b =>
    sum_nonneg fun p hp => mul_nonneg (hs0' p hp) (ind_nn _)
  have hx2nn : ∀ b, 0 ≤ x2 b := fun b =>
    sum_nonneg fun p hp => mul_nonneg (hs0' p hp) (ind_nn _)
  have hθnn : 0 ≤ θ := sum_nonneg fun p hp => mul_nonneg (hs0' p hp) (ind_nn _)
  have hx2θ : ∀ b, x2 b ≤ θ := by
    intro b
    apply sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (hs0' p hp)
    by_cases hc : C2 p <;> simp [hc]; split_ifs <;> norm_num
  -- Step D: the y's
  have hynn : ∀ b, 0 ≤ y1 b ∧ 0 ≤ y2 b ∧ 0 ≤ y3 b := by
    intro b
    refine ⟨sum_nonneg fun x hx => hq0 b x (mem_filter.mp hx).1,
      sum_nonneg fun x hx => hq0 b x (mem_filter.mp hx).1,
      sum_nonneg fun x hx => hq0 b x (mem_filter.mp hx).1⟩
  have hy123 : ∀ b ∈ U, y1 b + y2 b + y3 b = 1 := by
    intro b hbU
    have hb : t ≤ D.bid a b := (mem_filter.mp hbU).2
    rw [← hq1 b]
    simp only [y1, y2, y3, sum_filter, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    by_cases h1 : x < t
    · have : ¬ D.bid a b < x := by linarith
      simp [h1, this, not_le.mpr h1]
    · by_cases h2 : D.bid a b < x
      · simp [h1, h2, not_le.mpr h2]
      · push_neg at h1 h2; simp [h1, h2, not_lt.mpr h1, not_lt.mpr h2]
  -- Step E: probability bound
  have hprob : probRevGe D q a t = 1 - ∑ ρ ∈ roundings D, roundProb q ρ *
      (if revA D a ρ < t then 1 else 0) := by
    have hπ1 : ∑ ρ ∈ roundings D, roundProb q ρ = 1 := by
      unfold roundings roundProb; rw [← Finset.prod_univ_sum]; simp [hq1]
    unfold probRevGe
    have hsplit : ∑ ρ ∈ roundings D, roundProb q ρ * (if t ≤ revA D a ρ then 1 else 0) +
        ∑ ρ ∈ roundings D, roundProb q ρ * (if revA D a ρ < t then 1 else 0) =
        ∑ ρ ∈ roundings D, roundProb q ρ := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun ρ _ => ?_
      by_cases h : t ≤ revA D a ρ
      · simp [h, not_lt.mpr h]
      · simp [h, lt_of_not_ge h]
    linarith
  have hPlt := rlp53_prob_lt D q a t hq0 hq1
  rw [← hU] at hPlt
  -- monotonicity: L(y) ≤ L(x)
  have hmono := (rlp_L_mono U (fun b => 1 - x1 b - x2 b) x2 y3 y2
    (fun b _ => (hynn b).2.2)
    (fun b hb => by linarith [hy123 b hb, hx1y1 b hb, hx2y2 b hb])
    (fun b _ => hx2nn b) (fun b _ => (hynn b).2.1)
    (fun b hb => by linarith [hy123 b hb, hx1y1 b hb])).2
  have hx12 : ∀ b ∈ U, x1 b + x2 b ≤ 1 := fun b hb => by
    linarith [hy123 b hb, hx1y1 b hb, hx2y2 b hb, (hynn b).2.2]
  have h54 := (rlp_lemma54 U x1 x2 (fun b _ => hx1nn b) (fun b _ => hx2nn b) hx12).2
  set Aa := ∏ b ∈ U, (1 - x1 b)
  set T := ∏ b ∈ U, (1 - x2 b) + rlpSS U (fun b => 1 - x2 b) x2 with hT
  have hT1 : T ≤ 1 := (rlp_T_le_one U (fun b => 1 - x2 b) x2
    (fun b hb => by linarith [hx12 b hb, hx1nn b]) (fun b _ => hx2nn b)
    (fun b _ => by linarith)).2
  have hT0 : 0 ≤ T := add_nonneg (prod_nonneg fun b hb => by linarith [hx12 b hb, hx1nn b])
    (rlpSS_nonneg U _ x2 (fun b hb => by linarith [hx12 b hb, hx1nn b]) (fun b _ => hx2nn b))
  have hAexp : Aa ≤ Real.exp (-∑ b ∈ U, x1 b) :=
    rlp_prod_le_exp U x1 (fun b hb => by linarith [hx12 b hb, hx2nn b])
  have hσθ : ∑ b ∈ U, x1 b + θ ≤ 1 := by
    rw [← hmass]
    unfold profileMassGe
    refine le_trans ?_ (hs1 a)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun p hp _ => hs0' p hp)
  have hσ0 : 0 ≤ ∑ b ∈ U, x1 b := sum_nonneg fun b _ => hx1nn b
  have hmain : profileMassGe D s a t - probRevGe D q a t ≤ Real.exp (θ - 1) * T := by
    rw [hmass, hprob]
    have := rlp_scalar (∑ b ∈ U, x1 b) θ Aa T hσ0 hσθ hAexp hT0 hT1
    linarith
  refine hmain.trans ?_
  -- Step F: identify with Fobj
  let e := Fintype.equivFin B
  let z : B → ℝ := fun b => if t ≤ D.bid a b then x2 b else 0
  let xt : Fin (Fintype.card B) → ℝ := fun i => z (e.symm i)
  have hz1 : ∀ b, 1 - z b = if t ≤ D.bid a b then 1 - x2 b else 1 := by
    intro b; simp only [z]; split_ifs <;> simp
  have hP1 : ∏ i, (1 - xt i) = ∏ b ∈ U, (1 - x2 b) := by
    rw [Equiv.prod_comp e.symm (fun b => 1 - z b), hU, prod_filter]
    exact prod_congr rfl fun b _ => hz1 b
  have hinner : ∀ b, ∏ b' ∈ univ.erase b, (1 - z b') =
      if t ≤ D.bid a b then ∏ b' ∈ U.erase b, (1 - x2 b') else ∏ b' ∈ univ.erase b, (1 - z b') := by
    intro b
    split_ifs with hb
    · rw [hU, ← filter_erase, prod_filter]
      exact prod_congr rfl fun b' _ => hz1 b'
    · rfl
  have hS1 : ∑ i, xt i * ∏ j ∈ univ.erase i, (1 - xt j) = rlpSS U (fun b => 1 - x2 b) x2 := by
    have h1 : ∀ i, ∏ j ∈ univ.erase i, (1 - xt j) = ∏ b' ∈ univ.erase (e.symm i), (1 - z b') := by
      intro i
      apply Finset.prod_equiv e.symm
      · intro j; simp [e.symm.injective.eq_iff]
      · intro j _; rfl
    simp only [h1]
    rw [Equiv.sum_comp e.symm (fun b => z b * ∏ b' ∈ univ.erase b, (1 - z b'))]
    unfold rlpSS
    rw [hU, sum_filter, ← hU]
    refine sum_congr rfl fun b _ => ?_
    rw [hinner b]
    simp only [z]
    split_ifs <;> simp
  have hxsum : ∑ i, xt i = 2 * θ := by
    rw [Equiv.sum_comp e.symm z, ← hx2sum, hU, sum_filter]
  have hθ1 : θ ≤ 1 := by linarith
  have hfeas : OPTFeasible (Fintype.card B) θ xt := by
    refine ⟨fun i => ?_, ?_, fun i => ?_⟩
    · simp only [xt, z]; split_ifs
      · exact hx2nn _
      · exact le_rfl
    · rw [hxsum]; ring
    · simp only [xt, z]; split_ifs
      · exact hx2θ _
      · exact hθnn
  have hF : Fobj xt θ = Real.exp (θ - 1) * T := by
    unfold Fobj
    rw [hP1, hS1]
  rw [← hF]
  exact rlp_le_cOPT _ θ ⟨hθnn, hθ1⟩ xt hfeas
-- x
