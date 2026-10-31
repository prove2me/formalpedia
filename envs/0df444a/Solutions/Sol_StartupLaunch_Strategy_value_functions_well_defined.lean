-- Prove2me | solution 1 for StartupLaunch.Strategy.value_functions_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T03:17:50.664642+00:00
-- url     : https://prove2.me/submissions/f29e482b-a9b8-4f95-b50a-5909ae7b14b0

import Mathlib
import Definitions.Def_StartupLaunch_Strategy_Model

open StartupLaunch.Strategy

namespace StartupWDAux

/-- Contraction principle (see the explanation). -/
theorem contr {X : Type} (φ : X → ℝ) (K b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hK : ∀ x, φ x ≤ K) (h : ∀ x, φ x ≤ 0 ∨ ∃ y, φ x ≤ b * φ y) : ∀ x, φ x ≤ 0 := by
  have hK'pos : 0 < max K 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have key : ∀ n : ℕ, ∀ x, φ x ≤ b ^ n * max K 1 := by
    intro n
    induction n with
    | zero => intro x; simpa using (hK x).trans (le_max_left _ _)
    | succ n ih =>
      intro x
      rcases h x with h0 | ⟨y, hy⟩
      · exact h0.trans (by positivity)
      · calc φ x ≤ b * φ y := hy
          _ ≤ b * (b ^ n * max K 1) := mul_le_mul_of_nonneg_left (ih y) hb0
          _ = b ^ (n+1) * max K 1 := by ring
  intro x
  by_contra hx
  push_neg at hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hx hK'pos) hb1
  have := key n x
  rw [lt_div_iff₀ hK'pos] at hn
  linarith

noncomputable def DCt (P : Params) (p : ℝ) (f : Bool × ℝ → ℝ) (E : ℝ) : ℝ :=
  if P.c ≤ E then piDC P p (f (false, ED P E)) else 0

noncomputable def TopOp (P : Params) (p : ℝ) (f : Bool × ℝ → ℝ) : Bool × ℝ → ℝ
  | (true, E) => if P.c ≤ E + P.vo then max (piLS P) (piLC P p (f (true, EL P E))) else piLS P
  | (false, E) => if P.c ≤ E + P.vo then
      max (max (piLS P) (DCt P p f E)) (piLC P p (f (true, EL P E)))
      else max (piLS P) (DCt P p f E)

theorem rlc_eq (P : Params) (hδ : P.δ ≠ 0) (p : ℝ) (R1 : ℝ → ℝ) (E : ℝ) :
    RLC P p R1 E = E + piLC P p (R1 (EL P E) - EL P E) := by
  have h : P.δ * EL P E = E + P.vo - P.c := by unfold EL; field_simp
  unfold RLC piLC; linear_combination (1 - p) * h

theorem rdc_eq (P : Params) (hδ : P.δ ≠ 0) (p : ℝ) (R0 : ℝ → ℝ) (E : ℝ) :
    RDC P p R0 E = E + (if P.c ≤ E then piDC P p (R0 (ED P E) - ED P E) else 0) := by
  have h : P.δ * ED P E = E - P.c := by unfold ED; field_simp
  unfold RDC; split_ifs
  · unfold piDC; linear_combination (1 - p) * h
  · ring

theorem x1 (P : Params) (hδ : P.δ ≠ 0) (p : ℝ) (R0 R1 : ℝ → ℝ)
    (hR : StartupBellman P p R0 R1) (E : ℝ) :
    R1 E - E = if P.c ≤ E + P.vo then max (piLS P) (piLC P p (R1 (EL P E) - EL P E))
      else piLS P := by
  rw [hR.1 E]
  split_ifs
  · rw [rlc_eq P hδ, show RLS P E = E + piLS P from rfl, max_add_add_left]; ring
  · show E + piLS P - E = piLS P; ring

theorem x0 (P : Params) (hδ : P.δ ≠ 0) (p : ℝ) (R0 R1 : ℝ → ℝ)
    (hR : StartupBellman P p R0 R1) (E : ℝ) :
    R0 E - E = if P.c ≤ E + P.vo then
      max (max (piLS P) (if P.c ≤ E then piDC P p (R0 (ED P E) - ED P E) else 0))
        (piLC P p (R1 (EL P E) - EL P E))
      else max (piLS P) (if P.c ≤ E then piDC P p (R0 (ED P E) - ED P E) else 0) := by
  rw [hR.2.1 E]
  split_ifs <;>
  simp only [rlc_eq P hδ, rdc_eq P hδ, show RLS P E = E + piLS P from rfl, max_add_add_left,
    if_pos, if_neg, ↓reduceIte, *] <;> ring

/-- The established firm's equations (1)–(2) have a solution at every `q ∈ [0,1]`. -/
theorem est_exists (P : Params) (hP : P.Standing) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ Pi0 Pi1, EstBellman P q Pi0 Pi1 := by
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP
  obtain ⟨B, hBd⟩ : ∃ B, B = (1 - q) * P.δ := ⟨_, rfl⟩
  have hB : 0 < 1 - B := by rw [hBd]; nlinarith
  obtain ⟨A, hAd⟩ : ∃ A, A = P.vo - P.c + q * (1 - P.α) * P.δ * P.Va := ⟨_, rfl⟩
  obtain ⟨D, hDd⟩ : ∃ D, D = -P.c + q * (P.δ * P.Va) := ⟨_, rfl⟩
  have hLC : ∀ x, piLC P q x = A + B * x := by intro x; rw [hAd, hBd]; unfold piLC; ring
  have hDC : ∀ x, piDC P q x = D + B * x := by intro x; rw [hDd, hBd]; unfold piDC; ring
  have hF : A + B * (A / (1 - B)) = A / (1 - B) := by field_simp; ring
  have hG : D + B * (D / (1 - B)) = D / (1 - B) := by field_simp; ring
  have h1 : max (piLS P) (A / (1 - B)) =
      max (piLS P) (piLC P q (max (piLS P) (A / (1 - B)))) := by
    rw [hLC]
    rcases le_total (A / (1 - B)) (piLS P) with h | h
    · rw [max_eq_left h]
      have : A ≤ piLS P * (1 - B) := by rwa [div_le_iff₀ hB] at h
      rw [max_eq_left (show A + B * piLS P ≤ piLS P by linarith)]
    · rw [max_eq_right h, hF, max_eq_right h]
  refine ⟨max (max (piLS P) (A / (1 - B))) (D / (1 - B)), max (piLS P) (A / (1 - B)), ?_, h1⟩
  rw [← h1, hDC]
  rcases le_total (D / (1 - B)) (max (piLS P) (A / (1 - B))) with h | h
  · rw [max_eq_left h]
    have : D ≤ max (piLS P) (A / (1 - B)) * (1 - B) := by rwa [div_le_iff₀ hB] at h
    rw [max_eq_left (show D + B * max (piLS P) (A / (1 - B)) ≤ max (piLS P) (A / (1 - B)) by
      linarith)]
  · rw [max_eq_right h, hG, max_eq_right h]

end StartupWDAux

open StartupWDAux in
theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (∃ Pi0 Pi1 : ℝ, EstBellman P p Pi0 Pi1) ∧
    (∀ Pi0 Pi1 Pi0' Pi1' : ℝ, EstBellman P p Pi0 Pi1 → EstBellman P p Pi0' Pi1' →
      Pi0 = Pi0' ∧ Pi1 = Pi1') ∧
    (∃ R0 R1 : ℝ → ℝ, StartupBellman P p R0 R1) ∧
    (∀ R0 R1 R0' R1' : ℝ → ℝ, StartupBellman P p R0 R1 → StartupBellman P p R0' R1' →
      R0 = R0' ∧ R1 = R1') := by
  have hP' := hP
  obtain ⟨hvo, hvova, hvoc, hδ0, hδ1, hα0, hα1⟩ := hP'
  have hδ : P.δ ≠ 0 := hδ0.ne'
  have hVo : 0 < piLS P := by unfold piLS Params.Vo; exact div_pos hvo (by linarith)
  have hb0 : 0 ≤ (1 - p) * P.δ := mul_nonneg (by linarith) hδ0.le
  have hb1 : (1 - p) * P.δ < 1 := by nlinarith
  have hLCs : ∀ x y, piLC P p x - piLC P p y = (1 - p) * P.δ * (x - y) := by
    intro x y; unfold piLC; ring
  have hDCs : ∀ x y, piDC P p x - piDC P p y = (1 - p) * P.δ * (x - y) := by
    intro x y; unfold piDC; ring
  have hLCa : ∀ x y, |piLC P p x - piLC P p y| = (1 - p) * P.δ * |x - y| := by
    intro x y; rw [hLCs, abs_mul, abs_of_nonneg hb0]
  have hDCa : ∀ x y, |piDC P p x - piDC P p y| = (1 - p) * P.δ * |x - y| := by
    intro x y; rw [hDCs, abs_mul, abs_of_nonneg hb0]
  refine ⟨est_exists P hP p hp0 hp1, ?_, ?_, ?_⟩
  · -- uniqueness for the established firm
    rintro Pi0 Pi1 Pi0' Pi1' ⟨e0, e1⟩ ⟨e0', e1'⟩
    have h1 : |Pi1 - Pi1'| ≤ (1 - p) * P.δ * |Pi1 - Pi1'| := by
      rw [← hLCa]
      calc |Pi1 - Pi1'| = |max (piLS P) (piLC P p Pi1) - max (piLS P) (piLC P p Pi1')| := by
            rw [← e1, ← e1']
        _ ≤ max |piLS P - piLS P| |piLC P p Pi1 - piLC P p Pi1'| :=
            abs_max_sub_max_le_max _ _ _ _
        _ = |piLC P p Pi1 - piLC P p Pi1'| := by
            rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
    have h1' : Pi1 = Pi1' := by
      have : |Pi1 - Pi1'| ≤ 0 := by nlinarith [abs_nonneg (Pi1 - Pi1')]
      have := abs_nonpos_iff.1 this
      linarith
    refine ⟨?_, h1'⟩
    rw [← h1'] at e0'
    have h0 : |Pi0 - Pi0'| ≤ (1 - p) * P.δ * |Pi0 - Pi0'| := by
      rw [← hDCa]
      calc |Pi0 - Pi0'| = |max (max (piLS P) (piLC P p Pi1)) (piDC P p Pi0) -
              max (max (piLS P) (piLC P p Pi1)) (piDC P p Pi0')| := by rw [← e0, ← e0']
        _ ≤ max |max (piLS P) (piLC P p Pi1) - max (piLS P) (piLC P p Pi1)|
              |piDC P p Pi0 - piDC P p Pi0'| := abs_max_sub_max_le_max _ _ _ _
        _ = |piDC P p Pi0 - piDC P p Pi0'| := by
            rw [sub_self, abs_zero]; exact max_eq_right (abs_nonneg _)
    have : |Pi0 - Pi0'| ≤ 0 := by nlinarith [abs_nonneg (Pi0 - Pi0')]
    have := abs_nonpos_iff.1 this
    linarith
  · -- existence for the startup: Banach fixed point in the space of bounded functions
    have hRLS : ∀ E, RLS P E = E + piLS P := fun E => rfl
    obtain ⟨a0, ha0⟩ : ∃ a0, a0 = |piLC P p 0| + |piDC P p 0| + piLS P := ⟨_, rfl⟩
    have hbound : ∀ (f : Bool × ℝ → ℝ) (K : ℝ), 0 ≤ K → (∀ y, |f y| ≤ K) →
        ∀ x, |TopOp P p f x| ≤ a0 + (1 - p) * P.δ * K := by
      intro f K hK hf x
      have hA : ∀ y, piLC P p (f y) ≤ a0 + (1 - p) * P.δ * K := by
        intro y
        have h1 := hLCs (f y) 0
        have h2 := le_abs_self (piLC P p 0)
        have h3 := mul_le_mul_of_nonneg_left ((le_abs_self (f y)).trans (hf y)) hb0
        rw [ha0]; nlinarith [abs_nonneg (piDC P p 0)]
      have hD : ∀ E, DCt P p f E ≤ a0 + (1 - p) * P.δ * K := by
        intro E
        unfold DCt
        split_ifs
        · have h1 := hDCs (f (false, ED P E)) 0
          have h2 := le_abs_self (piDC P p 0)
          have h3 := mul_le_mul_of_nonneg_left ((le_abs_self (f (false, ED P E))).trans
            (hf (false, ED P E))) hb0
          rw [ha0]; nlinarith [abs_nonneg (piLC P p 0)]
        · rw [ha0]; nlinarith [abs_nonneg (piLC P p 0), abs_nonneg (piDC P p 0),
            mul_nonneg hb0 hK]
      have hV : piLS P ≤ a0 + (1 - p) * P.δ * K := by
        rw [ha0]; nlinarith [abs_nonneg (piLC P p 0), abs_nonneg (piDC P p 0),
            mul_nonneg hb0 hK]
      have hlow : piLS P ≤ TopOp P p f x := by
        rcases x with ⟨_ | _, E⟩ <;> simp only [TopOp] <;> split_ifs <;>
          simp only [le_max_iff, le_refl, true_or]
      have hup : TopOp P p f x ≤ a0 + (1 - p) * P.δ * K := by
        rcases x with ⟨_ | _, E⟩ <;> simp only [TopOp] <;> split_ifs
        · exact max_le (max_le hV (hD E)) (hA _)
        · exact max_le hV (hD E)
        · exact max_le hV (hA _)
        · exact hV
      rw [abs_le]; constructor <;> linarith
    have hlip : ∀ (f g : Bool × ℝ → ℝ) (K : ℝ), (∀ y, |f y - g y| ≤ K) →
        ∀ x, |TopOp P p f x - TopOp P p g x| ≤ (1 - p) * P.δ * K := by
      intro f g K hfg x
      have hK : 0 ≤ K := (abs_nonneg _).trans (hfg (true, 0))
      have hbK : 0 ≤ (1 - p) * P.δ * K := mul_nonneg hb0 hK
      have hA : ∀ y, |piLC P p (f y) - piLC P p (g y)| ≤ (1 - p) * P.δ * K := by
        intro y; rw [hLCa]; exact mul_le_mul_of_nonneg_left (hfg y) hb0
      have hD : ∀ E, |DCt P p f E - DCt P p g E| ≤ (1 - p) * P.δ * K := by
        intro E; unfold DCt; split_ifs
        · rw [hDCa]; exact mul_le_mul_of_nonneg_left (hfg _) hb0
        · rw [sub_self, abs_zero]; exact hbK
      have hVD : ∀ E, |max (piLS P) (DCt P p f E) - max (piLS P) (DCt P p g E)| ≤
          (1 - p) * P.δ * K := by
        intro E
        refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
        rw [sub_self, abs_zero]; exact max_le hbK (hD E)
      rcases x with ⟨_ | _, E⟩ <;> simp only [TopOp] <;> split_ifs
      · exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hVD E) (hA _))
      · exact hVD E
      · refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
        rw [sub_self, abs_zero]; exact max_le hbK (hA _)
      · rw [sub_self, abs_zero]; exact hbK
    have hnorm : ∀ (f : lp (fun _ : Bool × ℝ => ℝ) ⊤) (y : Bool × ℝ), |f y| ≤ ‖f‖ := by
      intro f y
      have := lp.norm_apply_le_norm ENNReal.top_ne_zero f y
      rwa [Real.norm_eq_abs] at this
    have hmem : ∀ f : lp (fun _ : Bool × ℝ => ℝ) ⊤, Memℓp (TopOp P p ⇑f) ⊤ := by
      intro f
      apply memℓp_infty
      refine ⟨a0 + (1 - p) * P.δ * ‖f‖, ?_⟩
      rintro _ ⟨x, rfl⟩
      show ‖TopOp P p (⇑f) x‖ ≤ _
      rw [Real.norm_eq_abs]
      exact hbound f ‖f‖ (norm_nonneg _) (hnorm f) x
    obtain ⟨T, hT⟩ : ∃ T : lp (fun _ : Bool × ℝ => ℝ) ⊤ → lp (fun _ : Bool × ℝ => ℝ) ⊤,
        ∀ f x, T f x = TopOp P p f x := ⟨fun f => ⟨TopOp P p f, hmem f⟩, fun f x => rfl⟩
    have hcon : ContractingWith ⟨(1 - p) * P.δ, hb0⟩ T := by
      refine ⟨NNReal.coe_lt_coe.1
        (show ((1 - p) * P.δ : ℝ) < ((1 : NNReal) : ℝ) by rw [NNReal.coe_one]; exact hb1),
        LipschitzWith.of_dist_le_mul fun f g => ?_⟩
      rw [dist_eq_norm, dist_eq_norm]
      show ‖T f - T g‖ ≤ (1 - p) * P.δ * ‖f - g‖
      apply lp.norm_le_of_forall_le (mul_nonneg hb0 (norm_nonneg _))
      intro x
      rw [lp.coeFn_sub, Pi.sub_apply, hT, hT, Real.norm_eq_abs]
      apply hlip
      intro y
      have := hnorm (f - g) y
      rwa [lp.coeFn_sub, Pi.sub_apply] at this
    obtain ⟨F, hF⟩ : ∃ F, T F = F :=
      ⟨ContractingWith.fixedPoint T hcon, ContractingWith.fixedPoint_isFixedPt hcon⟩
    have hfx : ∀ x, F x = TopOp P p F x := fun x => by rw [← hT, hF]
    refine ⟨fun E => E + F (false, E), fun E => E + F (true, E), ?_, ?_, ?_⟩
    · intro E
      show E + F (true, E) = _
      rw [rlc_eq P hδ]
      simp only [add_sub_cancel_left]
      rw [hfx (true, E)]
      simp only [TopOp]
      split_ifs
      · rw [hRLS, max_add_add_left]
      · rw [hRLS]
    · intro E
      show E + F (false, E) = _
      rw [rlc_eq P hδ, rdc_eq P hδ]
      simp only [add_sub_cancel_left]
      rw [hfx (false, E)]
      simp only [TopOp, DCt]
      split_ifs <;> simp only [hRLS, max_add_add_left]
    · refine ⟨‖F‖, fun E => ⟨?_, ?_⟩⟩
      · simp only [add_sub_cancel_left]; exact hnorm F _
      · simp only [add_sub_cancel_left]; exact hnorm F _
  · -- uniqueness for the startup
    intro R0 R1 R0' R1' hR hR'
    obtain ⟨M, hM⟩ := hR.2.2
    obtain ⟨M', hM'⟩ := hR'.2.2
    have hbd : ∀ (A B : ℝ → ℝ) (MA MB : ℝ), (∀ E, |A E - E| ≤ MA) → (∀ E, |B E - E| ≤ MB) →
        ∀ E, |(A E - E) - (B E - E)| ≤ MA + MB := by
      intro A B MA MB hA hB E
      have := abs_sub (A E - E) (B E - E)
      linarith [hA E, hB E]
    have u1 := contr (fun E => |(R1 E - E) - (R1' E - E)|) (M + M') ((1 - p) * P.δ) hb0 hb1
      (hbd R1 R1' M M' (fun E => (hM E).2) (fun E => (hM' E).2)) (by
        intro E
        rw [x1 P hδ p R0 R1 hR E, x1 P hδ p R0' R1' hR' E]
        split_ifs
        · right
          refine ⟨EL P E, ?_⟩
          rw [← hLCa]
          refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
          rw [sub_self, abs_zero]; exact max_le (abs_nonneg _) le_rfl
        · left; rw [sub_self, abs_zero])
    have hS1 : ∀ E, R1 E = R1' E := by
      intro E
      have := abs_nonpos_iff.1 (u1 E)
      linarith
    have u0 := contr (fun E => |(R0 E - E) - (R0' E - E)|) (M + M') ((1 - p) * P.δ) hb0 hb1
      (hbd R0 R0' M M' (fun E => (hM E).1) (fun E => (hM' E).1)) (by
        intro E
        rw [x0 P hδ p R0 R1 hR E, x0 P hδ p R0' R1' hR' E, hS1 (EL P E)]
        by_cases hc : P.c ≤ E
        · right
          refine ⟨ED P E, ?_⟩
          rw [if_pos hc, if_pos hc, ← hDCa]
          split_ifs
          · refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
            rw [sub_self, abs_zero]
            refine max_le ?_ (by positivity)
            refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
            rw [sub_self, abs_zero]; exact max_le (abs_nonneg _) le_rfl
          · refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
            rw [sub_self, abs_zero]; exact max_le (abs_nonneg _) le_rfl
        · left
          rw [if_neg hc, if_neg hc]
          split_ifs <;> rw [sub_self, abs_zero])
    refine ⟨funext fun E => ?_, funext hS1⟩
    have := abs_nonpos_iff.1 (u0 E)
    linarith
