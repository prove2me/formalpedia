-- Prove2me | solution 1 for WiretapFeedback.condIndep_message_decoded
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T05:34:10.904709+00:00
-- url     : https://prove2.me/submissions/f9096cc8-7c0b-480c-bf83-a3f47511f96a

import Mathlib
import Definitions.Def_WiretapFeedback_WiretapCode_law

open scoped ENNReal

namespace WiretapAux

open WiretapFeedback

variable {X O : Type} [Fintype O] {n : ℕ}

/-- Product formula for the law of the first `k` outputs given the local randomness. -/
lemma go_apply (S : FeedbackStrategy X O n) (W : WildeQIT.Channel X O) (ux : S.Ux) (uy : S.Uy) :
    ∀ (k : ℕ) (h : k ≤ n) (o : Fin k → O),
      FeedbackStrategy.runLaw.go S W ux uy k h o =
        ∏ s : Fin k, ENNReal.ofReal ((W (S.inputAt ⟨s.val, lt_of_lt_of_le s.isLt h⟩ ux uy
          (fun i => o ⟨i.val, lt_trans i.isLt s.isLt⟩))).prob (o s)) := by
  intro k
  induction k with
  | zero =>
    intro h o
    simp only [FeedbackStrategy.runLaw.go, Finset.univ_eq_empty, Finset.prod_empty]
    rw [PMF.pure_apply, if_pos (funext fun i => Fin.elim0 i)]
  | succ k ih =>
    intro h o
    simp only [FeedbackStrategy.runLaw.go]
    rw [PMF.bind_apply, tsum_eq_single (Fin.init o)]
    · rw [PMF.map_apply, tsum_eq_single (o (Fin.last k))]
      · rw [if_pos (Fin.snoc_init_self o).symm, ih (Nat.le_of_succ_le h) (Fin.init o),
          Fin.prod_univ_castSucc]
        unfold finDistPMF
        rw [PMF.ofFintype_apply]
        rfl
      · intro y hy
        rw [if_neg]
        intro heq
        apply hy
        rw [heq, Fin.snoc_last]
    · intro o' ho'
      rw [PMF.map_apply]
      refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun y => ?_)
      rw [if_neg]
      intro heq
      apply ho'
      rw [heq, Fin.init_snoc]

lemma runLaw_apply (S : FeedbackStrategy X O n) (W : WildeQIT.Channel X O) (ux : S.Ux)
    (uy : S.Uy) (o : Fin n → O) :
    S.runLaw W (ux, uy, o) = S.lawX ux * S.lawY uy * FeedbackStrategy.runLaw.go S W ux uy n le_rfl o := by
  unfold FeedbackStrategy.runLaw
  rw [PMF.bind_apply, tsum_eq_single ux]
  · rw [PMF.bind_apply, tsum_eq_single uy]
    · rw [PMF.map_apply, tsum_eq_single o]
      · rw [if_pos rfl, mul_assoc]
      · intro o' ho'
        rw [if_neg]
        intro h; exact ho' (congrArg (fun t => t.2.2) h).symm
    · intro uy' huy'
      refine mul_eq_zero_of_right _ ?_
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun o' => ?_
      rw [if_neg]
      intro h; exact huy' (congrArg (fun t => t.2.1) h).symm
  · intro ux' hux'
    refine mul_eq_zero_of_right _ ?_
    rw [PMF.bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun uy' => mul_eq_zero_of_right _ ?_
    rw [PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun o' => ?_
    rw [if_neg]
    intro h; exact hux' (congrArg (fun t => t.1) h).symm

section Code

variable {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}

lemma toStrategy_lawX (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (m : Fin N) (u : c.Ux) :
    (c.toStrategy Z μ).lawX (m, u) = μ m * c.lawX u := by
  show (μ.bind fun m => c.lawX.map fun u => (m, u)) (m, u) = _
  rw [PMF.bind_apply, tsum_eq_single m]
  · rw [PMF.map_apply, tsum_eq_single u]
    · simp
    · intro u' hu'
      rw [if_neg]
      intro h; exact hu' (congrArg Prod.snd h).symm
  · intro m' hm'
    refine mul_eq_zero_of_right _ ?_
    rw [PMF.map_apply]
    exact ENNReal.tsum_eq_zero.mpr fun u' => if_neg (fun h => hm' (congrArg Prod.fst h).symm)

/-- The feedback sequence produced from Bob's outputs `y` and his randomness. -/
def Fseq (c : WiretapCode X Y N n) (y : Fin n → Y) (uy : c.Uy) : Fin n → c.Fb :=
  fun s => c.feedback s (fun i => y ⟨i, lt_trans i.isLt s.isLt⟩) uy

/-- Eve's part `G(m)` of the factorised code law under the degraded channel. -/
noncomputable def Gpart (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (V₂ : WildeQIT.Channel X Z)
    (z : Fin n → Z) (f : Fin n → c.Fb) (m : Fin N) : ℝ≥0∞ :=
  μ m * ∑' u, c.lawX u * ∏ s : Fin n, ENNReal.ofReal
    ((V₂ (c.encoder s m u (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt s.isLt)⟩))).prob (z s))

open scoped Classical in
/-- Bob's part `H(m')` of the factorised code law under the degraded channel. -/
noncomputable def Hpart (c : WiretapCode X Y N n) (V₁ : WildeQIT.Channel Z Y)
    (z : Fin n → Z) (f : Fin n → c.Fb) (m' : Fin N) : ℝ≥0∞ :=
  ∑' uy, c.lawY uy * ∑ y : Fin n → Y,
    if m' = c.decoder y ∧ f = Fseq c y uy then
      ∏ s : Fin n, ENNReal.ofReal ((V₁ (z s)).prob (y s)) else 0

lemma law_apply (c : WiretapCode X Y N n) (μ : PMF (Fin N)) (V : WildeQIT.Channel X (Y × Z))
    (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y)
    (hV : ∀ x y z, (V x).prob (y, z) = (V₂ x).prob z * (V₁ z).prob y)
    (m m' : Fin N) (z : Fin n → Z) (f : Fin n → c.Fb) :
    c.law μ V (m, m', z, f) = Gpart c μ V₂ z f m * Hpart c V₁ z f m' := by
  classical
  unfold WiretapCode.law
  rw [PMF.map_apply]
  have hsplit : ∀ F : (Fin N × c.Ux) × c.Uy × (Fin n → Y × Z) → ℝ≥0∞,
      ∑' a, F a = ∑' (m0 : Fin N) (u : c.Ux) (uy : c.Uy) (o : Fin n → Y × Z), F ((m0, u), uy, o) := by
    intro F
    rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
    refine tsum_congr fun m0 => ?_
    refine tsum_congr fun u => ?_
    rw [ENNReal.tsum_prod']
  refine (hsplit _).trans ?_
  rw [tsum_eq_single m]
  swap
  · intro m0 hm0
    refine ENNReal.tsum_eq_zero.mpr fun u => ENNReal.tsum_eq_zero.mpr fun uy =>
      ENNReal.tsum_eq_zero.mpr fun o => ?_
    rw [if_neg]
    intro h
    exact hm0 (congrArg Prod.fst h).symm
  simp only
  -- the inner sum over the channel outputs
  have hinner : ∀ (u : c.Ux) (uy : c.Uy), (∑' o : Fin n → Y × Z,
      @ite _ ((m, m', z, f) = (m, c.decoder (fun s => (o s).1), (fun s => (o s).2),
        fun s => c.feedback s (fun i => (o ⟨i.val, lt_trans i.isLt s.isLt⟩).1) uy))
        (Classical.propDecidable _)
        (((WiretapCode.toStrategy Z c μ).runLaw V) ((m, u), uy, o)) 0) =
      (μ m * c.lawX u * ∏ s : Fin n, ENNReal.ofReal
        ((V₂ (c.encoder s m u (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt
          (Nat.succ_le_of_lt s.isLt)⟩))).prob (z s))) *
      (c.lawY uy * ∑ y : Fin n → Y, if m' = c.decoder y ∧ f = Fseq c y uy then
        ∏ s : Fin n, ENNReal.ofReal ((V₁ (z s)).prob (y s)) else 0) := by
    intro u uy
    rw [tsum_fintype]
    rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Y) (fun _ => Z)).symm]
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_eq_single z]
    · by_cases hc : m' = c.decoder y ∧ f = Fseq c y uy
      · rw [if_pos hc, if_pos]
        swap
        · simp only [Prod.mk.injEq, true_and]
          exact ⟨hc.1, rfl, hc.2⟩
        erw [runLaw_apply]
        rw [toStrategy_lawX]
        erw [go_apply]
        have hx : ∀ s : Fin n, (WiretapCode.toStrategy Z c μ).inputAt
            ⟨s.val, lt_of_lt_of_le s.isLt le_rfl⟩ (m, u) uy
            (fun i => ((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Y) (fun _ => Z)).symm
              (y, z)) ⟨i.val, lt_trans i.isLt s.isLt⟩) =
            c.encoder s m u (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt
              (Nat.succ_le_of_lt s.isLt)⟩) := by
          intro s
          rw [hc.2]
          rfl
        simp only [hx]
        have hprod : ∀ s : Fin n, ENNReal.ofReal ((V (c.encoder s m u (fun r => f ⟨r.val,
            lt_of_lt_of_le r.isLt (Nat.succ_le_of_lt s.isLt)⟩))).prob
            (((Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Y) (fun _ => Z)).symm (y, z)) s)) =
            ENNReal.ofReal ((V₂ (c.encoder s m u (fun r => f ⟨r.val, lt_of_lt_of_le r.isLt
              (Nat.succ_le_of_lt s.isLt)⟩))).prob (z s)) *
            ENNReal.ofReal ((V₁ (z s)).prob (y s)) := by
          intro s
          rw [← ENNReal.ofReal_mul (WildeQIT.FinDist.nonneg _ _)]
          congr 1
          exact hV _ (y s) (z s)
        simp only [hprod, Finset.prod_mul_distrib]
        have hY : (WiretapCode.toStrategy Z c μ).lawY uy = c.lawY uy := rfl
        erw [hY]
        ring
      · rw [if_neg hc, if_neg, mul_zero, mul_zero]
        simp only [Prod.mk.injEq, true_and, not_and]
        intro h1 _
        exact fun h3 => hc ⟨h1, h3⟩
    · intro z' _ hz'
      rw [if_neg]
      intro h
      exact hz' (congrArg (fun t => t.2.2.1) h).symm
    · simp
  refine (tsum_congr fun u => tsum_congr fun uy => hinner u uy).trans ?_
  unfold Gpart Hpart
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.tsum_mul_left, mul_assoc]

section Marginals

variable {A B C D : Type}

lemma map_snd_snd_apply (P : PMF (A × B × C × D)) (c : C) (d : D) :
    (P.map fun t => t.2.2) (c, d) = ∑' a, ∑' b, P (a, b, c, d) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun b => ?_
  rw [ENNReal.tsum_prod', tsum_eq_single c]
  · rw [tsum_eq_single d]
    · simp
    · intro d' hd'; rw [if_neg]; intro h; exact hd' (congrArg Prod.snd h).symm
  · intro c' hc'
    refine ENNReal.tsum_eq_zero.mpr fun d' => ?_
    rw [if_neg]; intro h; exact hc' (congrArg Prod.fst h).symm

lemma map_fst_snd_apply (P : PMF (A × B × C × D)) (a : A) (c : C) (d : D) :
    (P.map fun t => (t.1, t.2.2)) (a, c, d) = ∑' b, P (a, b, c, d) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod', tsum_eq_single a]
  · rw [ENNReal.tsum_prod']
    refine tsum_congr fun b => ?_
    rw [ENNReal.tsum_prod', tsum_eq_single c]
    · rw [tsum_eq_single d]
      · simp
      · intro d' hd'; rw [if_neg]; intro h; exact hd' (congrArg (fun t => t.2.2) h).symm
    · intro c' hc'
      refine ENNReal.tsum_eq_zero.mpr fun d' => ?_
      rw [if_neg]; intro h; exact hc' (congrArg (fun t => t.2.1) h).symm
  · intro a' ha'
    refine ENNReal.tsum_eq_zero.mpr fun bcd => ?_
    rw [if_neg]; intro h; exact ha' (congrArg Prod.fst h).symm

lemma map_snd_fst_apply (P : PMF (A × B × C × D)) (b : B) (c : C) (d : D) :
    (P.map fun t => (t.2.1, t.2.2)) (b, c, d) = ∑' a, P (a, b, c, d) := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_prod']
  refine tsum_congr fun a => ?_
  rw [ENNReal.tsum_prod', tsum_eq_single b]
  · rw [ENNReal.tsum_prod', tsum_eq_single c]
    · rw [tsum_eq_single d]
      · simp
      · intro d' hd'; rw [if_neg]; intro h; exact hd' (congrArg (fun t => t.2.2) h).symm
    · intro c' hc'
      refine ENNReal.tsum_eq_zero.mpr fun d' => ?_
      rw [if_neg]; intro h; exact hc' (congrArg (fun t => t.2.1) h).symm
  · intro b' hb'
    refine ENNReal.tsum_eq_zero.mpr fun cd => ?_
    rw [if_neg]; intro h; exact hb' (congrArg Prod.fst h).symm

end Marginals

end Code

end WiretapAux

open WiretapAux in
theorem solution {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ}
    (V : WildeQIT.Channel X (Y × Z)) (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y)
    (hV : ∀ x y z, (V x).prob (y, z) = (V₂ x).prob z * (V₁ z).prob y)
    (c : WiretapFeedback.WiretapCode X Y N n) (μ : PMF (Fin N)) :
    ∀ (m m' : Fin N) (z : Fin n → Z) (f : Fin n → c.Fb),
      c.law μ V (m, m', z, f) * ((c.law μ V).map fun t => t.2.2) (z, f) =
        ((c.law μ V).map fun t => (t.1, t.2.2)) (m, z, f) *
          ((c.law μ V).map fun t => (t.2.1, t.2.2)) (m', z, f) := by
  intro m m' z f
  rw [map_snd_snd_apply, map_fst_snd_apply, map_snd_fst_apply]
  simp only [law_apply c μ V V₂ V₁ hV]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  ring
