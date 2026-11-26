-- Prove2me | solution 1 for OCTKernel.Main.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T09:10:48.408405+00:00
-- url     : https://prove2.me/submissions/a3cb1462-96ec-4c64-b2c3-ca10cc438807

import Definitions.Def_OCTKernel_Main_Polynomials
import Theorems.Thm_OCTKernel_Main_lemma_3_2

open OCTKernel.Main Polynomial

private theorem root_order_bound {k : Type} [Field k] {s : ℕ}
    (g : Fin s → Polynomial k) (c : Fin s → k) (i : Fin s) (hi : c i ≠ 0)
    (a : k) (f : Polynomial k) (hrep : ∑ l, c l • g l = f)
    (hn : wronskian g ≠ 0) :
    f.rootMultiplicity a - (s - 1) ≤ (wronskian g).rootMultiplicity a := by
  classical
  let M : Matrix (Fin s) (Fin s) (Polynomial k) := fun l j => (derivative^[j.val]) (g l)
  let D : Polynomial k := (X - C a) ^ (f.rootMultiplicity a - (s-1))
  have hder (j : Fin s) : D ∣ (derivative^[j.val]) f := by
    exact (pow_dvd_pow _ (Nat.sub_le_sub_left (by omega : j.val ≤ s - 1) _)).trans
      (pow_sub_dvd_iterate_derivative_of_pow_dvd _ (pow_rootMultiplicity_dvd _ _))
  choose q hq using hder
  have hh : ∑ l, (C (c l)) • M l = D • q := by
    funext j
    calc
      _ = (derivative^[j.val]) (∑ l, c l • g l) := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, iterate_derivative_sum,
          iterate_derivative_smul, smul_eq_C_mul, iterate_derivative_C_mul, M]
      _ = D * q j := by rw [hrep, hq]
      _ = _ := rfl
  have hmul := Matrix.det_updateRow_sum M i (fun l => C (c l))
  rw [hh, Matrix.det_updateRow_smul, smul_eq_mul] at hmul
  have hdiv : D ∣ (C (c i)) * M.det := ⟨_, hmul.symm⟩
  have hunit : IsUnit (C (c i) : Polynomial k) := (isUnit_iff_ne_zero.mpr hi).map C
  apply (le_rootMultiplicity_iff hn).mpr
  change D ∣ M.det
  exact hdiv.trans ((associated_unit_mul_left _ _ hunit).dvd)

theorem solution (p s d : ℕ) [Fact p.Prime] (hs : 1 ≤ s) (hd : d < p)
    (W : Submodule (ZMod p) (Polynomial (ZMod p)))
    (hdim : Module.finrank (ZMod p) W = s)
    (hdeg : ∀ f ∈ W, f.degree ≤ (d : WithBot ℕ)) :
    ∑ α : ZMod p, (nu W α - (s - 1)) ≤ s * d := by
  classical
  letI : FiniteDimensional (ZMod p) W := .of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq (ZMod p) W hdim
  let g : Fin s → Polynomial (ZMod p) := fun i => (b i).1
  have hg : LinearIndependent (ZMod p) g :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype _)
  have hn : wronskian g ≠ 0 :=
    (OCTKernel.Main.lemma_3_2 p s d hs hd g (fun i => hdeg _ (b i).2)).mp hg
  have hpoint (a : ZMod p) : nu W a - (s-1) ≤ (wronskian g).rootMultiplicity a := by
    apply Nat.sub_le_iff_le_add.mpr
    apply csSup_le'
    rintro _ ⟨f,hf,hf0,rfl⟩
    let x : W := ⟨f,hf⟩
    let c : Fin s → ZMod p := fun l => b.repr x l
    have hrep : ∑ l, c l • g l = f := by
      dsimp only [c, g, x]
      simpa only [map_sum, map_smul, Submodule.subtype_apply, RingHom.id_apply] using
        congrArg W.subtype (b.sum_repr (⟨f, hf⟩ : W))
    obtain ⟨i,hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra! hh
      exact hf0 (by simpa [hh] using hrep.symm)
    have := root_order_bound g c i hi a f hrep hn
    omega
  calc
    _ ≤ ∑ a : ZMod p, (wronskian g).rootMultiplicity a := Finset.sum_le_sum fun a _ => hpoint a
    _ = (wronskian g).roots.card := by
      simp only [← count_roots]
      exact Multiset.sum_count_eq_card (by simp)
    _ ≤ (wronskian g).natDegree := card_roots' _
    _ ≤ s*d := by
      let A : Matrix (Fin s) (Fin s) (Polynomial (ZMod p)) :=
        Matrix.of fun i j => (derivative^[j.val]) (g i)
      change A.det.natDegree ≤ s * d
      rw [Matrix.det_apply A]
      apply natDegree_sum_le_of_forall_le
      intro σ _
      apply (natDegree_smul_le _ _).trans
      apply (natDegree_prod_le _ _).trans
      calc
        _ ≤ ∑ _ : Fin s, d := Finset.sum_le_sum fun j _ =>
          (natDegree_iterate_derivative _ _).trans <| (Nat.sub_le _ _).trans <|
          natDegree_le_iff_degree_le.mpr (hdeg _ (b (σ j)).2)
        _ = _ := by simp
