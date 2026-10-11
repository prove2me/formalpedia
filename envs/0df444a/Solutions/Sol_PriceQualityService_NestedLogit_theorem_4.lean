-- Prove2me | solution 1 for PriceQualityService.NestedLogit.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:29:28.20198+00:00
-- url     : https://prove2.me/submissions/93017c68-4dcb-48e3-8a00-3033b30c284c

import Mathlib
import Definitions.Def_PriceQualityService_NestedLogit_Optimum

namespace RRAux_PriceQualityService_NestedLogit_theorem_4

open PriceQualityService.NestedLogit

theorem term_le (y u : ℝ) : y * Real.exp u ≤ Real.exp (u + y - 1) := by
  rw [show u + y - 1 = (y - 1) + u by ring, Real.exp_add]
  have := Real.add_one_le_exp (y - 1)
  have hu := Real.exp_pos u
  nlinarith

theorem term_eq (y u : ℝ) (h : y * Real.exp u = Real.exp (u + y - 1)) : y = 1 := by
  by_contra hy
  have := Real.add_one_lt_exp (show y - 1 ≠ 0 from sub_ne_zero.mpr hy)
  rw [show u + y - 1 = (y - 1) + u by ring, Real.exp_add] at h
  have hu := Real.exp_pos u
  nlinarith

theorem one_d (μ : ℝ) (hμ : 0 < μ) (E V u r : ℝ) (hV : 0 < V) (hE : E = V * Real.exp (-u)) :
    E ^ (1 / μ) * (u - r) ≤ μ * (V * Real.exp (-r - μ)) ^ (1 / μ) ∧
    (E ^ (1 / μ) * (u - r) = μ * (V * Real.exp (-r - μ)) ^ (1 / μ) → u = r + μ) := by
  have hV' : 0 < V ^ (1 / μ) := Real.rpow_pos_of_pos hV _
  have e1 : E ^ (1 / μ) = V ^ (1 / μ) * Real.exp (-u * (1 / μ)) := by
    rw [hE, Real.mul_rpow hV.le (Real.exp_pos _).le, ← Real.exp_mul]
  have e2 : (V * Real.exp (-r - μ)) ^ (1 / μ) = V ^ (1 / μ) * Real.exp ((-r - μ) * (1 / μ)) := by
    rw [Real.mul_rpow hV.le (Real.exp_pos _).le, ← Real.exp_mul]
  have e3 : (-r - μ) * (1 / μ) = -u * (1 / μ) + (u - r) / μ - 1 := by
    field_simp; ring
  have hk := term_le ((u - r) / μ) (-u * (1 / μ))
  have hL : E ^ (1 / μ) * (u - r) =
      V ^ (1 / μ) * μ * ((u - r) / μ * Real.exp (-u * (1 / μ))) := by
    rw [e1]; field_simp
  have hR : μ * (V * Real.exp (-r - μ)) ^ (1 / μ) =
      V ^ (1 / μ) * μ * Real.exp (-u * (1 / μ) + (u - r) / μ - 1) := by
    rw [e2, e3]; ring
  have hpos : 0 < V ^ (1 / μ) * μ := mul_pos hV' hμ
  refine ⟨?_, fun heq => ?_⟩
  · rw [hL, hR]; exact mul_le_mul_of_nonneg_left hk hpos.le
  · rw [hL, hR] at heq
    have := term_eq _ _ (mul_left_cancel₀ hpos.ne' heq)
    field_simp at this
    linarith

theorem nest_chain (μ : ℝ) (hμ : 0 < μ) (n : ℕ) (U m : Fin n → ℝ) (r : ℝ) :
    ((∑ j, Real.exp (U j - m j)) ^ (1 / μ) / (∑ j, Real.exp (U j - m j))) *
        (∑ j, m j * Real.exp (U j - m j)) - r * (∑ j, Real.exp (U j - m j)) ^ (1 / μ) ≤
      μ * (∑ j, Real.exp (U j - r - μ)) ^ (1 / μ) ∧
    (((∑ j, Real.exp (U j - m j)) ^ (1 / μ) / (∑ j, Real.exp (U j - m j))) *
        (∑ j, m j * Real.exp (U j - m j)) - r * (∑ j, Real.exp (U j - m j)) ^ (1 / μ) =
      μ * (∑ j, Real.exp (U j - r - μ)) ^ (1 / μ) → ∀ j, m j = r + μ) := by
  have hμ1 : (1 / μ) ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.zero_rpow hμ1]
    refine ⟨by simp, fun _ j => j.elim0⟩
  set E := ∑ j, Real.exp (U j - m j) with hEdef
  set V := ∑ j, Real.exp (U j) with hVdef
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hEpos : 0 < E := Finset.sum_pos (fun j _ => Real.exp_pos _) hne
  have hVpos : 0 < V := Finset.sum_pos (fun j _ => Real.exp_pos _) hne
  set u := Real.log (V / E) with hu
  have hexpu : Real.exp (-u) = E / V := by
    rw [hu, Real.exp_neg, Real.exp_log (div_pos hVpos hEpos), inv_div]
  have hEVu : E = V * Real.exp (-u) := by rw [hexpu]; field_simp
  -- Gibbs, termwise
  have hg : ∀ j, m j * Real.exp (U j - m j) - u * Real.exp (U j - m j) ≤
      Real.exp (U j - u) - Real.exp (U j - m j) := by
    intro j
    have := term_le (m j - u + 1) (U j - m j)
    rw [show U j - m j + (m j - u + 1) - 1 = U j - u by ring] at this
    linarith
  have hsumexp : ∑ j, Real.exp (U j - u) = E := by
    simp only [sub_eq_add_neg, Real.exp_add, ← Finset.sum_mul]
    rw [hEVu]
  have hG : (∑ j, m j * Real.exp (U j - m j)) - u * E ≤ 0 := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hg j)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumexp] at this
    linarith
  have hsumr : ∑ j, Real.exp (U j - r - μ) = V * Real.exp (-r - μ) := by
    rw [hVdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Real.exp_add]; congr 1; ring
  obtain ⟨h1, h1eq⟩ := one_d μ hμ E V u r hVpos hEVu
  rw [hsumr]
  have hEr : 0 < E ^ (1 / μ) := Real.rpow_pos_of_pos hEpos _
  have hk : 0 < E ^ (1 / μ) / E := div_pos hEr hEpos
  have hstep : E ^ (1 / μ) / E * (∑ j, m j * Real.exp (U j - m j)) - r * E ^ (1 / μ) ≤
      E ^ (1 / μ) * (u - r) := by
    have := mul_le_mul_of_nonneg_left (show (∑ j, m j * Real.exp (U j - m j)) ≤ u * E by linarith)
      hk.le
    have e : E ^ (1 / μ) / E * (u * E) = E ^ (1 / μ) * u := by field_simp
    nlinarith
  refine ⟨hstep.trans h1, fun heq => ?_⟩
  have h2 : E ^ (1 / μ) * (u - r) = μ * (V * Real.exp (-r - μ)) ^ (1 / μ) := by
    linarith
  have hur := h1eq h2
  -- Gibbs equality
  have hGe : (∑ j, m j * Real.exp (U j - m j)) = u * E := by
    have e : E ^ (1 / μ) / E * (u * E) = E ^ (1 / μ) * u := by field_simp
    have : E ^ (1 / μ) / E * (∑ j, m j * Real.exp (U j - m j)) = E ^ (1 / μ) / E * (u * E) := by
      nlinarith
    exact mul_left_cancel₀ hk.ne' this
  have hz : ∑ j, ((Real.exp (U j - u) - Real.exp (U j - m j)) -
      (m j * Real.exp (U j - m j) - u * Real.exp (U j - m j))) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hsumexp, hGe]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hg j))] at hz
  intro j
  have := hz j (Finset.mem_univ _)
  have h3 : (m j - u + 1) * Real.exp (U j - m j) = Real.exp (U j - m j + (m j - u + 1) - 1) := by
    rw [show U j - m j + (m j - u + 1) - 1 = U j - u by ring]; linarith
  have := term_eq _ _ h3
  linarith


theorem sum_nest (f : Nest → ℝ) : ∑ x, f x = f Nest.s + f Nest.l := by
  show ∑ x ∈ ({Nest.s, Nest.l} : Finset Nest), f x = _
  rw [Finset.sum_pair (by decide)]

theorem att_eq (M : Model) (p q : Vec M) (x : Nest) (j : Fin (M.m x)) :
    attraction M p q x j = Real.exp (netUtility M q x j - markup M p q x j) := by
  unfold attraction netUtility markup; congr 1; ring

theorem U_le (M : Model) (hc : ∀ x i, 0 < M.c x i) (q : Vec M) (x : Nest) (i : Fin (M.m x)) :
    netUtility M q x i ≤ netUtility M (qDagger M) x i ∧
    (netUtility M q x i = netUtility M (qDagger M) x i → q x i = qDagger M x i) := by
  have hci := hc x i
  have h2 : 2 * M.c x i * qDagger M x i = M.α x i + M.t x * M.b x i := by
    unfold qDagger; field_simp
  have hd : netUtility M (qDagger M) x i - netUtility M q x i =
      M.c x i * (qDagger M x i - q x i) ^ 2 := by
    unfold netUtility; linear_combination (q x i - qDagger M x i) * h2
  refine ⟨?_, fun h => ?_⟩
  · have : 0 ≤ M.c x i * (qDagger M x i - q x i) ^ 2 := by positivity
    linarith
  · rw [h, sub_self] at hd
    have := (mul_eq_zero.mp hd.symm).resolve_left hci.ne'
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith

noncomputable def LHSx (M : Model) (p q : Vec M) (r : ℝ) (x : Nest) : ℝ :=
  (nestAttraction M p q x ^ (1 / M.μ₁) / nestAttraction M p q x) *
    (∑ j, markup M p q x j * attraction M p q x j) - r * nestAttraction M p q x ^ (1 / M.μ₁)

noncomputable def RHSx (M : Model) (q : Vec M) (r : ℝ) (x : Nest) : ℝ :=
  M.μ₁ * (∑ j, Real.exp (netUtility M q x j - r - M.μ₁)) ^ (1 / M.μ₁)

theorem chain (M : Model) (hμ : 0 < M.μ₁) (p q : Vec M) (r : ℝ) (x : Nest) :
    LHSx M p q r x ≤ RHSx M q r x ∧
    (LHSx M p q r x = RHSx M q r x → ∀ j, markup M p q x j = r + M.μ₁) := by
  have := nest_chain M.μ₁ hμ (M.m x) (netUtility M q x) (markup M p q x) r
  unfold LHSx RHSx nestAttraction
  simp only [att_eq]
  exact this

theorem rhs_mono (M : Model) (hμ : 0 < M.μ₁) (hc : ∀ x i, 0 < M.c x i) (q : Vec M) (r : ℝ)
    (x : Nest) : RHSx M q r x ≤ RHSx M (qDagger M) r x := by
  unfold RHSx
  apply mul_le_mul_of_nonneg_left _ hμ.le
  apply Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) _ (by positivity)
  exact Finset.sum_le_sum fun j _ => Real.exp_le_exp.mpr (by
    have := (U_le M hc q x j).1; linarith)

theorem fp_eq (M : Model) (q : Vec M) (r : ℝ) :
    fixedPointRHS M q r = ∑ x, RHSx M q r x := rfl

theorem nestAtt_nonneg (M : Model) (p q : Vec M) (x : Nest) : 0 ≤ nestAttraction M p q x :=
  Finset.sum_nonneg fun j _ => (Real.exp_pos _).le

theorem denom_pos (M : Model) (p q : Vec M) :
    0 < 1 + nestAttraction M p q Nest.s ^ (1 / M.μ₁) + nestAttraction M p q Nest.l ^ (1 / M.μ₁) := by
  have h1 := Real.rpow_nonneg (nestAtt_nonneg M p q Nest.s) (1 / M.μ₁)
  have h2 := Real.rpow_nonneg (nestAtt_nonneg M p q Nest.l) (1 / M.μ₁)
  linarith

-- profit - r, scaled by the denominator
theorem profit_identity (M : Model) (p q : Vec M) (r : ℝ) :
    (profit M p q - r) *
      (1 + nestAttraction M p q Nest.s ^ (1 / M.μ₁) + nestAttraction M p q Nest.l ^ (1 / M.μ₁)) =
      (∑ x, LHSx M p q r x) - r := by
  have hD := (denom_pos M p q).ne'
  have hp : profit M p q *
      (1 + nestAttraction M p q Nest.s ^ (1 / M.μ₁) + nestAttraction M p q Nest.l ^ (1 / M.μ₁)) =
      ∑ x, (nestAttraction M p q x ^ (1 / M.μ₁) / nestAttraction M p q x) *
        (∑ j, markup M p q x j * attraction M p q x j) := by
    unfold profit
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold choiceProb nestProb condProb
    field_simp
  unfold LHSx
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_nest (fun x => nestAttraction M p q x ^ (1 / M.μ₁)),
    sub_mul, hp]
  ring

end RRAux_PriceQualityService_NestedLogit_theorem_4

open PriceQualityService.NestedLogit in
open RRAux_PriceQualityService_NestedLogit_theorem_4 in
-- Theorem 4, p. 19 (Wang, Ke & Cui)
theorem solution (M : Model) (hμ : 1 ≤ M.μ₁) (hc : ∀ x i, 0 < M.c x i) :
    ∃ rDag : ℝ,
      rDag = fixedPointRHS M (qDagger M) rDag ∧
      (∀ r : ℝ, r = fixedPointRHS M (qDagger M) r → r = rDag) ∧
      (∀ p q : Vec M, profit M p q ≤ profit M (pDagger M rDag) (qDagger M)) ∧
      profit M (pDagger M rDag) (qDagger M) = rDag ∧
      (∀ p q : Vec M, (∀ p' q' : Vec M, profit M p' q' ≤ profit M p q) →
        q = qDagger M ∧ p = pDagger M rDag) := by
  have hμ0 : 0 < M.μ₁ := by linarith
  have hexp : 0 < 1 / M.μ₁ := by positivity
  set F : ℝ → ℝ := fun r => fixedPointRHS M (qDagger M) r with hF
  have Fnn : ∀ r, 0 ≤ F r := fun r => Finset.sum_nonneg fun x _ =>
    mul_nonneg hμ0.le (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) _)
  have Fanti : ∀ r1 r2, r1 ≤ r2 → F r2 ≤ F r1 := by
    intro r1 r2 h
    refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ hμ0.le
    refine Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) ?_ hexp.le
    exact Finset.sum_le_sum fun j _ => Real.exp_le_exp.mpr (by linarith)
  have Fcont : Continuous F := by
    simp only [hF, fixedPointRHS]
    refine continuous_finsetSum _ fun x _ => continuous_const.mul ?_
    exact Continuous.rpow_const (by fun_prop) (fun _ => Or.inr hexp.le)
  obtain ⟨R, hR⟩ : ∃ R, R = F R := by
    have hcont : ContinuousOn (fun r : ℝ => r - F r) (Set.Icc 0 (F 0)) :=
      (continuous_id.sub Fcont).continuousOn
    have h0 : (0:ℝ) - F 0 ≤ 0 := by have := Fnn 0; linarith
    have h1 : 0 ≤ F 0 - F (F 0) := by have := Fanti 0 (F 0) (Fnn 0); linarith
    obtain ⟨R, _, hR⟩ := intermediate_value_Icc (Fnn 0) hcont ⟨h0, h1⟩
    exact ⟨R, by simp only at hR; linarith⟩
  have huniq : ∀ r, r = F r → r = R := by
    intro r hr
    rcases le_total r R with h | h
    · have := Fanti r R h; linarith
    · have := Fanti R r h; linarith
  -- upper bound
  have hbound : ∀ p q : Vec M, profit M p q ≤ R := by
    intro p q
    have hid := profit_identity M p q R
    have hD := denom_pos M p q
    have hs : ∑ x, LHSx M p q R x ≤ R := by
      have : ∑ x, LHSx M p q R x ≤ ∑ x, RHSx M (qDagger M) R x :=
        Finset.sum_le_sum fun x _ => (chain M hμ0 p q R x).1.trans (rhs_mono M hμ0 hc q R x)
      rw [← fp_eq] at this
      have hR' : fixedPointRHS M (qDagger M) R = R := hR.symm
      linarith
    have : (profit M p q - R) *
      (1 + nestAttraction M p q Nest.s ^ (1 / M.μ₁) + nestAttraction M p q Nest.l ^ (1 / M.μ₁)) ≤ 0 := by
      rw [hid]; linarith
    have := nonpos_of_mul_nonpos_left this hD
    linarith
  -- attained
  have hval : profit M (pDagger M R) (qDagger M) = R := by
    have hid := profit_identity M (pDagger M R) (qDagger M) R
    have hD := denom_pos M (pDagger M R) (qDagger M)
    have hx : ∀ x, LHSx M (pDagger M R) (qDagger M) R x = RHSx M (qDagger M) R x := by
      intro x
      have hmk : ∀ j, markup M (pDagger M R) (qDagger M) x j = M.μ₁ + R := by
        intro j; unfold markup pDagger; ring
      have hE : nestAttraction M (pDagger M R) (qDagger M) x =
          ∑ j, Real.exp (netUtility M (qDagger M) x j - R - M.μ₁) := by
        unfold nestAttraction
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [att_eq, hmk]; congr 1; ring
      unfold LHSx RHSx
      simp only [hmk, ← Finset.mul_sum]
      rw [show (∑ j, attraction M (pDagger M R) (qDagger M) x j) =
        nestAttraction M (pDagger M R) (qDagger M) x from rfl, ← hE]
      generalize nestAttraction M (pDagger M R) (qDagger M) x = E
      rcases eq_or_ne E 0 with h0 | h0
      · subst h0; simp [Real.zero_rpow (show M.μ₁⁻¹ ≠ 0 by positivity)]
      · field_simp; ring
    have hs : ∑ x, LHSx M (pDagger M R) (qDagger M) R x = R := by
      rw [Finset.sum_congr rfl (fun x _ => hx x), ← fp_eq]; exact hR.symm
    rw [hs, sub_self] at hid
    have := (mul_eq_zero.mp hid).resolve_right hD.ne'
    linarith
  refine ⟨R, hR, huniq, fun p q => by rw [hval]; exact hbound p q, hval, ?_⟩
  intro p q hmax
  have hpq : profit M p q = R := le_antisymm (hbound p q) (by
    have := hmax (pDagger M R) (qDagger M); rw [hval] at this; exact this)
  have hid := profit_identity M p q R
  rw [hpq, sub_self, zero_mul] at hid
  have hsum : ∑ x, LHSx M p q R x = ∑ x, RHSx M (qDagger M) R x := by
    rw [← fp_eq]; have : fixedPointRHS M (qDagger M) R = R := hR.symm; linarith
  have hle1 : ∀ x, LHSx M p q R x ≤ RHSx M q R x := fun x => (chain M hμ0 p q R x).1
  have hle2 : ∀ x, RHSx M q R x ≤ RHSx M (qDagger M) R x := fun x => rhs_mono M hμ0 hc q R x
  rw [sum_nest, sum_nest] at hsum
  have heq : ∀ x, LHSx M p q R x = RHSx M q R x ∧ RHSx M q R x = RHSx M (qDagger M) R x := by
    have a1 := hle1 Nest.s; have a2 := hle1 Nest.l
    have b1 := hle2 Nest.s; have b2 := hle2 Nest.l
    intro x; cases x
    · constructor <;> linarith
    · constructor <;> linarith
  have hq : q = qDagger M := by
    funext x i
    have h := (heq x).2
    unfold RHSx at h
    have h' := mul_left_cancel₀ hμ0.ne' h
    have hA := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      (Real.exp_pos (netUtility M q x j - R - M.μ₁)).le
    have hB := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) =>
      (Real.exp_pos (netUtility M (qDagger M) x j - R - M.μ₁)).le
    have hsums : ∑ j, Real.exp (netUtility M q x j - R - M.μ₁) =
        ∑ j, Real.exp (netUtility M (qDagger M) x j - R - M.μ₁) :=
      le_antisymm ((Real.rpow_le_rpow_iff hA hB hexp).mp h'.le)
        ((Real.rpow_le_rpow_iff hB hA hexp).mp h'.ge)
    have hterm : ∀ j, Real.exp (netUtility M q x j - R - M.μ₁) ≤
        Real.exp (netUtility M (qDagger M) x j - R - M.μ₁) := fun j =>
      Real.exp_le_exp.mpr (by have := (U_le M hc q x j).1; linarith)
    have hz : ∑ j, (Real.exp (netUtility M (qDagger M) x j - R - M.μ₁) -
        Real.exp (netUtility M q x j - R - M.μ₁)) = 0 := by
      rw [Finset.sum_sub_distrib, hsums, sub_self]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hterm j))] at hz
    have := Real.exp_injective (sub_eq_zero.mp (hz i (Finset.mem_univ _)))
    exact (U_le M hc q x i).2 (by linarith)
  refine ⟨hq, ?_⟩
  funext x i
  have hm := (chain M hμ0 p q R x).2 (heq x).1 i
  have hqi : q x i = qDagger M x i := by rw [hq]
  unfold markup at hm
  unfold pDagger
  rw [hqi] at hm
  linarith

#print axioms solution
