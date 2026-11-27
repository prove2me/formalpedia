-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.JLatOf.stepMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:18.410277+00:00
-- url     : https://prove2.me/submissions/10fc3eec-5048-493b-a2a0-29b9568f81a7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_LatticeReduction_LatticeHeightZeroEq
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_Mj_eq_span
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_finrank_Mj
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_gmap_span
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_span_basis_coe
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_exists_frame
import Theorems.Thm_PositivityTheory_Rg_Rs_JLatOf_lattice_height_zero_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.JLatOf
open PositivityTheory.Rg.Rs
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.Rg.Rs.JLatOf
theorem _root_.solution [Finite k] (n : ℕ) (M : Submodule k (Fin (n + 1) → k)) (hM : e0 k n ∈ M) :
    ∃ (jj : Fin (n + 1)) (g : GL (Fin (n + 1)) k), (jj : ℕ) + finrank k M = n + 1 ∧
      gmap g (Mj k (n + 1) jj) = M ∧ gmap g (Mj k (n + 1) (jj + 1)) = M ⊓ H0 k n ∧
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single jj 1 = e0 k n ∧
      ∀ b : Fin (n + 1), jj < b → (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 b = 0 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, r = finrank k M := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hbot
    rw [hbot, Submodule.mem_bot] at hM
    have h5 : (Pi.single (0 : Fin (n + 1)) (1 : k) : Fin (n + 1) → k) 0 = 0 := congrFun hM 0
    simp at h5
  have hrle : r ≤ n + 1 := by
    rw [hr]
    exact (Submodule.finrank_le M).trans (by simp)
  have hH0 : finrank k (H0 k n) = n := by
    rw [lattice_height_zero_eq, finrank_Mj _ _ (by omega)]
    simp
  have hsup : M ⊔ H0 k n = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • e0 k n + (x - x 0 • e0 k n) := by abel
    rw [hx]
    apply Submodule.add_mem_sup (Submodule.smul_mem _ _ hM)
    delta H0 e0
    simp
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq M (H0 k n)
  rw [hsup, finrank_top, Module.finrank_fin_fun, hH0, ← hr] at hdim
  obtain ⟨m, hm⟩ : ∃ m, m = r - 1 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Submodule k (Fin (n + 1) → k), P = M ⊓ H0 k n := ⟨_, rfl⟩
  rw [← hP] at hdim
  have hdimMH : finrank k ↥P = m := by omega
  obtain ⟨b⟩ : Nonempty (Basis (Fin m) k ↥P) := ⟨Module.finBasisOfFinrankEq k _ hdimMH⟩
  obtain ⟨v, hv_def⟩ : ∃ v : Fin m → Fin (n + 1) → k, v = fun i => (b i : Fin (n + 1) → k) := ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : Fin (m + 1) → Fin (n + 1) → k, u = Fin.cons (e0 k n) v := ⟨_, rfl⟩
  have hvli : LinearIndependent k v := by
    rw [hv_def]
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hspanv : Submodule.span k (Set.range v) = M ⊓ H0 k n := by
    rw [hv_def, ← hP]
    exact span_basis_coe b
  have hvmem : ∀ i, v i ∈ M ⊓ H0 k n := by
    intro i
    rw [hv_def, ← hP]
    exact (b i).2
  have he0 : e0 k n ∉ H0 k n := by
    delta H0 e0
    simp
  have hu : LinearIndependent k u := by
    rw [hu_def, linearIndependent_finCons]
    refine ⟨hvli, ?_⟩
    rw [hspanv]
    intro hmem
    exact he0 (Submodule.mem_inf.mp hmem).2
  have hsum : (m + 1) + (n + 1 - r) = n + 1 := by omega
  obtain ⟨g, hg⟩ := exists_frame (n + 1) (n + 1 - r) (m + 1) hsum u hu
  refine ⟨⟨n + 1 - r, by omega⟩, g, by simp only; omega, ?_, ?_, ?_, ?_⟩
  · show gmap g (Mj k (n + 1) (n + 1 - r)) = M
    rw [Mj_eq_span (n + 1) (n + 1 - r) (m + 1) hsum, gmap_span]
    simp only [hg]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [hu_def]
        simpa using hM
      · simp only [hu_def, Fin.cons_succ]
        exact (Submodule.mem_inf.mp (hvmem i)).1
    · rw [finrank_span_eq_card hu]
      simp
      omega
  · have hsum' : m + (n + 1 - r + 1) = n + 1 := by omega
    show gmap g (Mj k (n + 1) (n + 1 - r + 1)) = M ⊓ H0 k n
    rw [Mj_eq_span (n + 1) (n + 1 - r + 1) m hsum', gmap_span]
    have hgv : ∀ i : Fin m, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ ej (n + 1) (n + 1 - r + 1) m hsum' i = v i := by
      intro i
      have hej : ej (k := k) (n + 1) (n + 1 - r + 1) m hsum' i = ej (n + 1) (n + 1 - r) (m + 1) hsum i.succ := by
        simp only [ej]
        congr 1
        ext
        simp
        omega
      rw [hej, hg i.succ, hu_def, Fin.cons_succ]
    simp only [hgv]
    exact hspanv
  · have hej : ej (k := k) (n + 1) (n + 1 - r) (m + 1) hsum 0 = Pi.single ⟨n + 1 - r, by omega⟩ 1 := by
      simp only [ej]
      congr 1
    rw [← hej, hg 0, hu_def]
    rfl
  · intro bb hbb
    have hbb' : n + 1 - r < (bb : ℕ) := hbb
    have hi : (bb : ℕ) - (n + 1 - r + 1) < m := by omega
    let i : Fin m := ⟨(bb : ℕ) - (n + 1 - r + 1), hi⟩
    have hej : ej (k := k) (n + 1) (n + 1 - r) (m + 1) hsum i.succ = Pi.single bb 1 := by
      simp only [ej]
      congr 1
      ext
      simp [i]
      omega
    have h1 := hg i.succ
    rw [hej] at h1
    have h3 : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single bb 1) 0 = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 bb := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← h3, h1, hu_def, Fin.cons_succ]
    exact (Submodule.mem_inf.mp (hvmem i)).2
end PositivityTheory.Rg.Rs.JLatOf
