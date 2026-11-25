-- Prove2me | solution 1 for PI.BeDiagZp.beDiagZp_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:34:38.465472+00:00
-- url     : https://prove2.me/submissions/fc697759-408b-432c-af8e-241f36b2b671

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SimeqCongr
import Theorems.Thm_PI_BeDiagZp_Asm_simeq_congr
import Theorems.Thm_PI_BeDiagZp_Asm_intX
import Theorems.Thm_PI_BeDiagZp_Asm_int0
import Theorems.Thm_PI_BeDiagZp_Asm_ccX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp
open Asm
namespace PI.BeDiagZp
theorem _root_.solution (h0 : S0) (h1 : S1) (h2 : SubstOps) (h3 : Ident) (h4 : Cont) (h5 : IntSubst) :
    Target := by
  intro p _ l ex ph S hex hlex hswap hint hgrp hz hphi hconj hbi
  obtain ⟨hl0, hI⟩ := h3 p l ex hex hlex

  have rfl' : ∀ {σ : Type} (f : MvPowerSeries σ ℂ_[p]), Simeq f f := fun f => (h0 p _ f f f f f).1
  have symm' : ∀ {σ : Type} {f g : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq g f :=
    fun {σ} {f g} h => (h0 p σ f g g g g).2.1 h
  have trans' : ∀ {σ : Type} {f g k : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq g k → Simeq f k :=
    fun {σ} {f g k} a b => (h0 p σ f g k f f).2.2.1 a b
  have add' : ∀ {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq f' g' →
      Simeq (f + f') (g + g') :=
    fun {σ} {f g f' g'} a b => (h0 p σ f g f f' g').2.2.2 a b

  have cA : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → MvPowerSeries.constantCoeff (add l ex a b) = 0 :=
    fun a b ha hb => (hI _ a b ha hb).1
  have cM : ∀ {σ : Type} (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 :=
    fun c a ha => (hI _ a a ha ha).2.1 c
  have comm : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → add l ex a b = add l ex b a :=
    fun a b ha hb => (hI _ a b ha hb).2.2.1
  have add2 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      add l ex a a = mulBy l ex 2 a :=
    fun a ha => (hI _ a a ha ha).2.2.2.1
  have addM : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      ∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.1
  have addS : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      ∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.1
  have mul1 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      mulBy l ex 1 a = a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.2.1
  have mul0 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      mulBy l ex 0 a = 0 :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.2.2
  have bsym : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → be l ex ph a b = be l ex ph b a := by
    intro σ a b ha hb
    simp only [be]
    rw [comm a b ha hb]
    abel

  have addZ : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      add l ex a 0 = a := by
    intro σ a ha
    have e := addM a ha 1 0
    rw [mul1 a ha, mul0 a ha, add_zero, mul1 a ha] at e
    exact e
  have ccU : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := ccX ()

  have K1 : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv ())) (Xv ()) : MvPowerSeries Unit ℂ_[p])
      (be l ex ph (Xv ()) (mulBy l ex α.2 (Xv ()))) := by
    intro α hα
    have H := h1 p (Fin 2) Unit _ _ (fun _ => (Xv () : MvPowerSeries Unit ℂ_[p])) (fun _ => ccU)
      (fun _ => intX ()) (hconj α hα)
    obtain ⟨hsX, -, -, hr⟩ := h2 p l ex ph hex hl0 (Fin 2) Unit
      (fun _ => (Xv () : MvPowerSeries Unit ℂ_[p])) (fun _ => ccU)
    have e1 := (hr _ _ (cM α.1 _ (ccX (0 : Fin 2))) (ccX (1 : Fin 2))).2.2.2.2
    have e2 := (hr _ _ (ccX (0 : Fin 2)) (cM α.2 _ (ccX (1 : Fin 2)))).2.2.2.2
    have e3 := (hr _ _ (ccX (0 : Fin 2)) (ccX (0 : Fin 2))).2.2.1 α.1
    have e4 := (hr _ _ (ccX (1 : Fin 2)) (ccX (1 : Fin 2))).2.2.1 α.2
    simp only [e1, e2, e3, e4, hsX] at H
    exact H

  have K2 : ∀ a b c : MvPowerSeries Unit ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → MvPowerSeries.constantCoeff c = 0 →
      IntegralMv a → IntegralMv b → IntegralMv c →
      Simeq (be l ex ph (add l ex a b) c) (be l ex ph a c + be l ex ph b c) := by
    intro a b c ha hb hc ia ib ic
    have hs : ∀ i, MvPowerSeries.constantCoeff (![a, b, c] i) = 0 := by
      intro i; fin_cases i <;> simpa
    have is : ∀ i, IntegralMv (![a, b, c] i) := by
      intro i; fin_cases i <;> simpa
    have H := h1 p (Fin 3) Unit _ _ ![a, b, c] hs is hbi
    obtain ⟨hsX, -, hsA, hr⟩ := h2 p l ex ph hex hl0 (Fin 3) Unit ![a, b, c] hs
    have e1 := (hr _ _ (cA _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))) (ccX (2 : Fin 3))).2.2.2.2
    have e2 := (hr _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))).2.1
    have e3 := (hr _ _ (ccX (0 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
    have e4 := (hr _ _ (ccX (1 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
    simp only [hsA, e1, e2, e3, e4, hsX] at H
    simpa using H

  have K0 : Simeq (be l ex ph (Xv ()) (mulBy l ex ((0 : ℕ) : ℂ_[p]) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C ((0 : ℕ) : ℂ_[p]) * be l ex ph (Xv ()) (Xv ())) := by
    have H := symm' (K2 0 0 0 (map_zero _) (map_zero _) (map_zero _) int0 int0 int0)
    have z00 : add l ex (0 : MvPowerSeries Unit ℂ_[p]) 0 = 0 := addZ 0 (map_zero _)
    refine simeq_congr ?_ H
    rw [Nat.cast_zero, mul0 _ ccU, map_zero, zero_mul, sub_zero]
    simp only [be, z00, addZ _ ccU]
    abel

  have K3 : ∀ n : ℕ, IntegralMv (mulBy l ex (n : ℂ_[p]) (Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
      Simeq (be l ex ph (Xv ()) (mulBy l ex (n : ℂ_[p]) (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv ()) (Xv ())) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, K0⟩
      rw [Nat.cast_zero, mul0 _ ccU]
      exact int0
    | succ n ih =>
      obtain ⟨iN, hN⟩ := ih
      have cN := cM (n : ℂ_[p]) _ ccU
      have eS : mulBy l ex ((n + 1 : ℕ) : ℂ_[p]) (Xv ()) =
          add l ex (mulBy l ex (n : ℂ_[p]) (Xv ())) (Xv () : MvPowerSeries Unit ℂ_[p]) := by
        rw [addS _ ccU, Nat.cast_succ]
      rw [eS]
      refine ⟨?_, ?_⟩
      · have hs : ∀ i, MvPowerSeries.constantCoeff
            (![mulBy l ex (n : ℂ_[p]) (Xv ()), (Xv () : MvPowerSeries Unit ℂ_[p])] i) = 0 := by
          intro i; fin_cases i <;> simpa
        have is : ∀ i, IntegralMv
            (![mulBy l ex (n : ℂ_[p]) (Xv ()), (Xv () : MvPowerSeries Unit ℂ_[p])] i) := by
          intro i; fin_cases i
          · simpa using iN
          · simpa using (intX () : IntegralMv (Xv () : MvPowerSeries Unit ℂ_[p]))
        have H := h5 p (Fin 2) Unit _ _ hs is hgrp
        obtain ⟨hsX, -, -, hr⟩ := h2 p l ex ph hex hl0 (Fin 2) Unit _ hs
        rw [(hr _ _ (ccX (0 : Fin 2)) (ccX (1 : Fin 2))).2.1, hsX, hsX] at H
        simpa using H
      · rw [bsym _ _ ccU (cA _ _ cN ccU)]
        have H := K2 _ _ _ cN ccU ccU iN (intX ()) (intX ())
        rw [bsym _ _ cN ccU] at H
        have H2 := trans' H (add' hN (rfl' (be l ex ph (Xv ()) (Xv ()))))
        have e : MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv ()) (Xv ()) + be l ex ph (Xv ()) (Xv ()) =
            (MvPowerSeries.C ((n + 1 : ℕ) : ℂ_[p]) * be l ex ph (Xv ()) (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
          rw [Nat.cast_succ, map_add, map_one, add_mul, one_mul]
        rw [e] at H2
        exact H2
  have K4 := h4 p l ex ph hex hl0 (fun n => (K3 n).2)
  refine ⟨?_, ?_⟩
  · intro γ hγ
    obtain ⟨n, hn⟩ := hz γ hγ
    have ia : IntegralMv (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) := hint γ hγ
    have ib : IntegralMv (mulBy l ex γ.2 (Xv ()) : MvPowerSeries Unit ℂ_[p]) := hint γ.swap (hswap γ hγ)
    have ca := cM γ.1 _ ccU
    have cb := cM γ.2 _ ccU

    have C1 := K1 γ.swap (hswap γ hγ)
    simp only [Prod.fst_swap, Prod.snd_swap] at C1
    rw [bsym _ _ cb ccU] at C1

    have H := K2 _ _ _ ca cb ccU ia ib (intX ())
    rw [addM _ ccU, hn, bsym _ _ (cM _ _ ccU) ccU, bsym _ _ ca ccU, bsym _ _ cb ccU] at H
    have A := add' (rfl' (be l ex ph (Xv ()) (mulBy l ex γ.1 (Xv ())))) (symm' C1)
    have B := trans' (trans' A (symm' H)) (K4 n)
    rw [← hn] at B
    rw [two_mul]
    exact B
  · refine simeq_congr ?_ hphi
    simp only [be, add2 _ ccU]
    rw [map_mul, map_ofNat]
    ring
end PI.BeDiagZp
