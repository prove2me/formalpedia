-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:27.418664+00:00
-- url     : https://prove2.me/submissions/226b785d-c31b-4d71-99d1-f5add6c25462

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_mono
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLt_zero_eq
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaLe_pred
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaGt_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_eq_zero_of_le_gt
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LC_B3_op_sum__6a1d2ce1b97d
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_adj_comm_K
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_op_inj
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_closure_prop
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_smul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_symK_op


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.B3
theorem _root_.solution (hC : CompSt) (hF : FFTSym) (hFFT : PositivityTheory.Rg.Sw.FFT) (ε : Fin m → Bool) :
    ∀ N (s : Sym m n), SymbolInFirstFamily ε s → (∀ i j, symK ε i j s = 0) → EtaLe s N →
      ∃ w ∈ PA (n := n) ε, ∀ f, op s f = w f := by
  classical
  have hLe_add : ∀ {u v : Sym m n} {d : ℕ}, EtaLe u d → EtaLe v d → EtaLe (u + v) d := by
    intro u v d hu hv t ht
    rcases Finset.mem_union.1 (support_add ht) with h | h
    exacts [hu t h, hv t h]
  have hLe_neg : ∀ {u : Sym m n} {d : ℕ}, EtaLe u d → EtaLe (-u) d := fun hu t ht => hu t (by rwa [support_neg] at ht)
  have hLe_sum : ∀ {ι : Type} (T : Finset ι) (u : ι → Sym m n) {d : ℕ}, (∀ i ∈ T, EtaLe (u i) d) →
      EtaLe (∑ i ∈ T, u i) d := fun T u d hu =>
    Finset.sum_induction _ (fun r => EtaLe r d) (fun _ _ => hLe_add) (fun t ht => by simp at ht) hu
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro s hs hK hN
  have hmem := hF hFFT m n ε s hs hK
  have hmem' : s ∈ Submodule.span ℂ (Submonoid.closure (Set.range fun ab : Fin m × Fin m => pairSym (n := n) ε ab.1 ab.2) : Set (Sym m n)) := by
    rw [← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]
    exact hmem
  rw [Submodule.mem_span_set'] at hmem'
  obtain ⟨k, c, g, hsum⟩ := hmem'
  choose d hde hdf w hw r hrf hrl hop using fun i => closure_prop hC ε (SetLike.mem_coe.1 (g i).2)
  have hsT : s = ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • (g i : Sym m n) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i ≤ N) (fun i => c i • (g i : Sym m n))
    rw [hsum] at hsplit
    have hz : ∑ i ∈ Finset.univ.filter (fun i => ¬ d i ≤ N), c i • (g i : Sym m n) = 0 := by
      apply eq_zero_of_le_gt (N := N)
      · have he : ∑ i ∈ Finset.univ.filter (fun i => ¬ d i ≤ N), c i • (g i : Sym m n) =
            s + -(∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • (g i : Sym m n)) := by
          rw [← hsplit]
          abel
        rw [he]
        refine hLe_add hN (hLe_neg (hLe_sum _ _ fun i hi => fun t ht => ?_))
        exact (hde i t (support_smul ht)).trans_le (Finset.mem_filter.1 hi).2
      · refine etaGt_sum _ _ fun i hi => fun t ht => ?_
        have e1 : ed t = d i := hde i t (support_smul ht)
        have e2 := (Finset.mem_filter.1 hi).2
        show N < ed t
        omega
    rw [hz, add_zero] at hsplit
    exact hsplit.symm
  have hWmem : (∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • w i) ∈ PA (n := n) ε :=
    Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (hw i) _
  set W := ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • w i with hWdef
  set R := ∑ i ∈ Finset.univ.filter (fun i => d i ≤ N), c i • r i with hRdef
  have hopS : ∀ f, op s f = W f - op R f := by
    intro f
    rw [hsT, op_sum', hRdef, op_sum', hWdef, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [op_smul, op_smul, LinearMap.smul_apply, hop i f, op_add, smul_add, add_sub_cancel_right]
  have hR : ∀ f, op R f = W f - op s f := fun f => by
    rw [hopS]
    abel
  have hRK : ∀ i j, symK ε i j R = 0 := by
    intro i j
    apply op_inj
    intro f
    have hc := adj_comm_K ε i j hWmem
    have hs0 := symK_op ε i j s f
    rw [hK i j, op_zero] at hs0
    rw [symK_op, hR, hR, map_sub]
    have e1 : KopL ε i j (W f) = W (KopL ε i j f) := by
      have := congrArg (fun F : Module.End ℂ (PX m n) => F f) hc
      simpa [Module.End.mul_apply] using this.symm
    rw [e1, sub_eq_zero.1 hs0.symm]
    abel
  have hRf : SymbolInFirstFamily ε R := symmetric_filtration_sum _ _ fun i _ => symmetric_filtration_smul _ (hrf i)
  have hRlt : EtaLt R N := etaLt_sum _ _ fun i hi => etaLt_smul _ (etaLt_mono (hrl i) (Finset.mem_filter.1 hi).2)
  by_cases hN0 : N = 0
  · subst hN0
    have hR0 := etaLt_zero_eq hRlt
    refine ⟨W, hWmem, fun f => ?_⟩
    rw [hopS, hR0, op_zero, sub_zero]
  · obtain ⟨wR, hwR, hwRop⟩ := ih (N - 1) (by omega) R hRf hRK (etaLe_pred hRlt)
    refine ⟨W - wR, Subalgebra.sub_mem _ hWmem hwR, fun f => ?_⟩
    rw [hopS, hwRop, LinearMap.sub_apply]
end PositivityTheory.Rg.Sw.LC.B3
