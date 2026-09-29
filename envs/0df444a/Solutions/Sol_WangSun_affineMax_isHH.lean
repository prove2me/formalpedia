-- Prove2me | solution 1 for WangSun.affineMax_isHH
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T05:50:38.252879+00:00
-- url     : https://prove2.me/submissions/931c6862-2eb6-4e19-afce-f150c205ed70

import Definitions.Def_CPWL
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.Dual.Lemmas

open Finset

namespace WangSun

abbrev E (n : ℕ) := Fin n → ℝ
abbrev Aff (n : ℕ) := E n →ᵃ[ℝ] ℝ

private lemma affine_sum_linear {n : ℕ} {I : Type} [DecidableEq I]
    (s : Finset I) (w : I → ℝ) (L : I → Aff n) :
    (∑ i ∈ s, w i • L i).linear = ∑ i ∈ s, w i • (L i).linear := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert, hi, AffineMap.add_linear, ih]

private lemma affine_sum_apply {n : ℕ} {I : Type} [DecidableEq I]
    (s : Finset I) (w : I → ℝ) (L : I → Aff n) (x : E n) :
    (∑ i ∈ s, w i • L i) x = ∑ i ∈ s, w i * L i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert, hi, ih]

theorem large_affine_family_partition {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (L : I → Aff n) (hcard : n + 1 < Fintype.card I) :
    ∃ (S T : Finset I) (hS : S.Nonempty) (hT : T.Nonempty),
      Disjoint S T ∧ S ∪ T = Finset.univ ∧
        ∀ x, S.inf' hS (fun i => L i x) ≤ T.sup' hT (fun i => L i x) := by
  let p : I → (E n →ₗ[ℝ] ℝ) := fun i => (L i).linear
  have hfinrank : Module.finrank ℝ (E n →ₗ[ℝ] ℝ) = n := by
    rw [Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hdep : ¬ AffineIndependent ℝ p := by
    intro hp
    have hc := hp.card_le_finrank_succ
    have hspan : Module.finrank ℝ (vectorSpan ℝ (Set.range p)) ≤
        Module.finrank ℝ (E n →ₗ[ℝ] ℝ) := Submodule.finrank_le _
    rw [hfinrank] at hspan
    exact (not_le_of_gt hcard) (hc.trans (Nat.add_le_add_right hspan 1))
  rw [affineIndependent_iff] at hdep
  push_neg at hdep
  obtain ⟨s, w, hsum, hlin, i₀, hi₀, hwi₀⟩ := hdep
  have hpos : ∃ i ∈ s, 0 < w i :=
    exists_pos_of_sum_zero_of_exists_nonzero w hsum ⟨i₀, hi₀, hwi₀⟩
  let T₀ : Finset I := s.filter fun i => 0 < w i
  let S₀ : Finset I := s.filter fun i => w i ≤ 0
  have hT₀ : T₀.Nonempty := by
    rcases hpos with ⟨i, hi, hwi⟩
    exact ⟨i, by simp [T₀, hi, hwi]⟩
  have hsplit : S₀ ∪ T₀ = s := by
    ext i
    simp only [S₀, T₀, mem_union, mem_filter]
    constructor
    · aesop
    · intro hi
      rcases lt_or_ge 0 (w i) with hwi | hwi
      · exact Or.inr ⟨hi, hwi⟩
      · exact Or.inl ⟨hi, hwi⟩
  have hdisj : Disjoint S₀ T₀ := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    simp only [S₀, mem_filter] at hiS
    simp only [T₀, mem_filter] at hiT
    exact (not_lt_of_ge hiS.2) hiT.2
  have hS₀ : S₀.Nonempty := by
    by_contra hS
    rw [not_nonempty_iff_eq_empty] at hS
    have hsT : T₀ = s := by simpa [hS] using hsplit
    have hallpos : ∀ i ∈ s, 0 < w i := by
      intro i hi
      have : i ∈ T₀ := by simpa [hsT]
      exact (mem_filter.mp this).2
    have hsome : ∃ i ∈ s, 0 < w i := by
      refine ⟨hT₀.choose, ?_, ?_⟩
      · simpa [← hsT] using hT₀.choose_spec
      · exact hallpos _ (by simpa [← hsT] using hT₀.choose_spec)
    have : 0 < ∑ i ∈ s, w i :=
      Finset.sum_pos' (fun i hi => (hallpos i hi).le) hsome
    linarith
  let a : ℝ := ∑ i ∈ T₀, w i
  have ha : 0 < a := Finset.sum_pos'
    (fun i hi => (mem_filter.mp hi).2.le)
    ⟨hT₀.choose, hT₀.choose_spec, (mem_filter.mp hT₀.choose_spec).2⟩
  let F : Aff n := ∑ i ∈ s, w i • L i
  have hFlinear : F.linear = 0 := by
    dsimp [F]
    rw [affine_sum_linear]
    simpa [p] using hlin
  have hFconst : ∀ x, F x = F 0 := by
    intro x
    rw [AffineMap.decomp F]
    simp [hFlinear]
  have hweightS : ∑ i ∈ S₀, (-w i) = a := by
    have hparts : (∑ i ∈ s, w i) =
        (∑ i ∈ S₀, w i) + ∑ i ∈ T₀, w i := by
      rw [← hsplit, sum_union hdisj]
    dsimp [a]
    rw [hparts] at hsum
    rw [sum_neg_distrib]
    linarith
  let U : Finset I := Finset.univ \ s
  let z : I := hT₀.choose
  let S : Finset I := S₀ ∪ U
  let T : Finset I := T₀
  have hzT : z ∈ T := hT₀.choose_spec
  have hST : S ∪ T = Finset.univ := by
    dsimp [S, T, U, T₀, S₀]
    ext i
    by_cases hi : i ∈ s
    · by_cases hwi : 0 < w i
      · simp [hi, hwi]
      · simp [hi, hwi, le_of_not_gt hwi]
    · simp [hi]
  have hSTdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    rcases mem_union.mp hiS with hiS₀ | hiU
    · exact (Finset.disjoint_left.mp hdisj) hiS₀ hiT
    · have hiT₀ : i ∈ T₀ := by simpa [T] using hiT
      exact (mem_sdiff.mp hiU).2 (mem_filter.mp hiT₀).1
  have hS : S.Nonempty := hS₀.mono subset_union_left
  have hT : T.Nonempty := hT₀
  by_cases hc : 0 ≤ F 0
  · refine ⟨S, T, hS, hT, hSTdisj, hST, ?_⟩
    intro x
    have hmax : a * (T.sup' hT fun i => L i x) ≥ ∑ i ∈ T₀, w i * L i x := by
      calc
        ∑ i ∈ T₀, w i * L i x ≤
            ∑ i ∈ T₀, w i * (T.sup' hT fun i => L i x) := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun i => L i x) (show i ∈ T from hi))
            (le_of_lt (mem_filter.mp hi).2)
        _ = a * (T.sup' hT fun i => L i x) := by
          dsimp [a, T]
          rw [sum_mul]
    have hmin : a * (S.inf' hS fun i => L i x) ≤
        ∑ i ∈ S₀, (-w i) * L i x := by
      calc
        a * (S.inf' hS fun i => L i x) =
            ∑ i ∈ S₀, (-w i) * (S.inf' hS fun i => L i x) := by
          rw [← hweightS, sum_mul]
        _ ≤ ∑ i ∈ S₀, (-w i) * L i x := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (Finset.inf'_le _ (show i ∈ S from subset_union_left hi))
            (neg_nonneg.mpr (mem_filter.mp hi).2)
    have hFx : 0 ≤ F x := by rw [hFconst]; exact hc
    have hdecomp : F x =
        (∑ i ∈ T₀, w i * L i x) - ∑ i ∈ S₀, (-w i) * L i x := by
      dsimp [F]
      rw [← hsplit, sum_union hdisj]
      simp only [AffineMap.coe_add, Pi.add_apply]
      rw [affine_sum_apply, affine_sum_apply]
      have hneg : (∑ i ∈ S₀, w i * L i x) =
          -(∑ i ∈ S₀, (-w i) * L i x) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro i hi
        ring
      rw [hneg]
      ring
    rw [hdecomp] at hFx
    nlinarith
  · have hc' : 0 ≤ (-F) 0 := by simp; linarith
    let S' : Finset I := T₀ ∪ U
    let T' : Finset I := S₀
    have hST' : S' ∪ T' = Finset.univ := by
      dsimp [S', T', U, T₀, S₀]
      ext i
      by_cases hi : i ∈ s
      · by_cases hwi : 0 < w i
        · simp [hi, hwi]
        · simp [hi, hwi, le_of_not_gt hwi]
      · simp [hi]
    have hSTdisj' : Disjoint S' T' := by
      rw [Finset.disjoint_left]
      intro i hiS hiT
      rcases mem_union.mp hiS with hiT₀ | hiU
      · exact (Finset.disjoint_left.mp hdisj) hiT hiT₀
      · have hiS₀ : i ∈ S₀ := by simpa [T'] using hiT
        exact (mem_sdiff.mp hiU).2 (mem_filter.mp hiS₀).1
    have hS' : S'.Nonempty := hT₀.mono subset_union_left
    have hT' : T'.Nonempty := hS₀
    refine ⟨S', T', hS', hT', hSTdisj', hST', ?_⟩
    intro x
    have hmax : a * (T'.sup' hT' fun i => L i x) ≥
        ∑ i ∈ S₀, (-w i) * L i x := by
      calc
        ∑ i ∈ S₀, (-w i) * L i x ≤
            ∑ i ∈ S₀, (-w i) * (T'.sup' hT' fun i => L i x) := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun i => L i x) (show i ∈ T' from hi))
            (neg_nonneg.mpr (mem_filter.mp hi).2)
        _ = a * (T'.sup' hT' fun i => L i x) := by
          rw [← hweightS, sum_mul]
    have hmin : a * (S'.inf' hS' fun i => L i x) ≤
        ∑ i ∈ T₀, w i * L i x := by
      calc
        a * (S'.inf' hS' fun i => L i x) =
            ∑ i ∈ T₀, w i * (S'.inf' hS' fun i => L i x) := by
          dsimp [a]
          rw [sum_mul]
        _ ≤ ∑ i ∈ T₀, w i * L i x := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left
            (Finset.inf'_le _ (show i ∈ S' from subset_union_left hi))
            (le_of_lt (mem_filter.mp hi).2)
    have hFx : 0 ≤ (-F) x := by
      simp only [AffineMap.coe_neg, Pi.neg_apply]
      rw [hFconst]
      simpa only [AffineMap.coe_neg, Pi.neg_apply] using hc'
    have hdecomp : (-F) x =
        (∑ i ∈ S₀, (-w i) * L i x) - ∑ i ∈ T₀, w i * L i x := by
      dsimp [F]
      rw [← hsplit, sum_union hdisj]
      simp only [AffineMap.coe_neg, Pi.neg_apply, AffineMap.coe_add, Pi.add_apply]
      rw [affine_sum_apply, affine_sum_apply]
      have hneg : (∑ i ∈ S₀, (-w i) * L i x) =
          -(∑ i ∈ S₀, w i * L i x) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro i hi
        ring
      rw [hneg]
      ring
    rw [hdecomp] at hFx
    nlinarith


private def toggle {I : Type} [DecidableEq I] (i : I) (M : Finset I) : Finset I :=
  if i ∈ M then M.erase i else insert i M

private lemma alternating_powerset_sum_eq_zero {I : Type} [DecidableEq I]
    (S : Finset I) (i : I) (hi : i ∈ S) (q : Finset I → ℝ)
    (hq : ∀ M ∈ S.powerset, q M = q (toggle i M)) :
    ∑ M ∈ S.powerset, (-1 : ℝ) ^ M.card * q M = 0 := by
  apply sum_involution (s := S.powerset) (f := fun M => (-1 : ℝ) ^ M.card * q M)
      (fun M _ => toggle i M)
  · intro M hM
    by_cases hiM : i ∈ M
    · have hqM := hq M hM
      simp only [toggle, hiM, if_pos] at hqM ⊢
      rw [← card_erase_add_one hiM, pow_succ, hqM]
      ring
    · have hqM := hq M hM
      simp [toggle, hiM] at hqM ⊢
      rw [pow_succ, ← hqM]
      ring
  · intro M hM hne
    by_cases hiM : i ∈ M <;> simp [toggle, hiM]
  · intro M hM
    rw [mem_powerset] at hM ⊢
    by_cases hiM : i ∈ M
    · simp only [toggle, hiM, if_pos]
      exact (erase_subset _ _).trans hM
    · simp only [toggle, hiM, if_neg]
      exact insert_subset hi hM
  · intro M hM
    by_cases hiM : i ∈ M
    · simp [toggle, hiM]
    · simp [toggle, hiM]

theorem alternating_max_identity {n : ℕ} {I : Type} [DecidableEq I]
    (L : I → Aff n) (S T : Finset I) (hS : S.Nonempty) (hT : T.Nonempty)
    (hdom : ∀ x, S.inf' hS (fun i => L i x) ≤ T.sup' hT (fun i => L i x)) :
    ∀ x, ∑ M ∈ S.powerset, (-1 : ℝ) ^ M.card *
        ((M ∪ T).sup' (hT.mono subset_union_right) fun i => L i x) = 0 := by
  intro x
  obtain ⟨i, hiS, hi⟩ := Finset.exists_mem_eq_inf' hS (fun i => L i x)
  let q : Finset I → ℝ := fun M =>
    (M ∪ T).sup' (hT.mono subset_union_right) fun i => L i x
  have hpair (M : Finset I) (hiM : i ∉ M) : q M = q (insert i M) := by
    dsimp [q]
    apply le_antisymm
    · apply Finset.sup'_le _ _
      intro j hj
      apply Finset.le_sup' (fun i => L i x)
      simp only [mem_union, mem_insert]
      rcases mem_union.mp hj with hjM | hjT
      · exact Or.inl (Or.inr hjM)
      · exact Or.inr hjT
    · apply Finset.sup'_le _ _
      intro j hj
      rcases mem_union.mp hj with hjN | hjT
      · rcases mem_insert.mp hjN with hji | hjM
        · rw [hji]
          calc
            L i x = S.inf' hS (fun j => L j x) := hi.symm
            _ ≤ T.sup' hT (fun j => L j x) := hdom x
            _ ≤ (M ∪ T).sup' (hT.mono subset_union_right) (fun j => L j x) := by
              apply Finset.sup'_le _ _
              intro k hk
              exact Finset.le_sup' (fun j => L j x) (mem_union_right M hk)
        · exact Finset.le_sup' (fun j => L j x) (mem_union_left T hjM)
      · exact Finset.le_sup' (fun j => L j x) (mem_union_right M hjT)
  apply alternating_powerset_sum_eq_zero S i hiS q
  intro M hM
  by_cases hiM : i ∈ M
  · simp only [toggle, hiM, if_pos]
    have hnot : i ∉ M.erase i := notMem_erase i M
    have hp := hpair (M.erase i) hnot
    rw [insert_erase hiM] at hp
    exact hp.symm
  · simp only [toggle, hiM, if_neg]
    exact hpair M hiM


private lemma isHH_zero {n : ℕ} : IsHH (fun _ : E n => (0 : ℝ)) := by
  let h : Fin 0 → (E n → ℝ) := Fin.elim0
  refine ⟨0, h, ?_, ?_⟩
  · intro k
    exact Fin.elim0 k
  · funext x
    simp

private lemma isHH_add {n : ℕ} {f g : E n → ℝ} (hf : IsHH f) (hg : IsHH g) :
    IsHH (f + g) := by
  rcases hf with ⟨K, h, hh, rfl⟩
  rcases hg with ⟨L, q, hq, rfl⟩
  let terms : Fin (K + L) → (E n → ℝ) := Fin.addCases h q
  refine ⟨K + L, terms, ?_, ?_⟩
  · intro i
    refine Fin.addCases (motive := fun i => IsHinge (terms i)) ?_ ?_ i
    · intro j
      simpa [terms] using hh j
    · intro j
      simpa [terms] using hq j
  · rw [Fin.sum_univ_add]
    simp [terms]

private lemma isHH_neg {n : ℕ} {f : E n → ℝ} (hf : IsHH f) : IsHH (-f) := by
  rcases hf with ⟨K, h, hh, rfl⟩
  refine ⟨K, fun k => -h k, ?_, ?_⟩
  · intro k
    rcases hh k with ⟨σ, A, hσ, hk⟩
    refine ⟨-σ, A, ?_, ?_⟩
    · rcases hσ with rfl | rfl <;> simp
    · change -h k = _
      rw [hk]
      funext x
      simp
  · funext x
    simp

private lemma isHH_signed {n k : ℕ} {f : E n → ℝ} (hf : IsHH f) :
    IsHH (fun x => (-1 : ℝ) ^ k * f x) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      have hn := isHH_neg ih
      have hfe : (fun x => (-1 : ℝ) ^ (k + 1) * f x) = -(fun x => (-1 : ℝ) ^ k * f x) := by
        funext x; rw [Pi.neg_apply]; ring
      rw [hfe]; exact hn

private lemma isHH_finset_sum {n : ℕ} {A : Type} [DecidableEq A]
    (s : Finset A) (f : A → E n → ℝ) (hf : ∀ a ∈ s, IsHH (f a)) :
    IsHH (∑ a ∈ s, f a) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isHH_zero (n := n)
  | @insert a s ha ih =>
      rw [sum_insert ha]
      exact isHH_add (hf a (mem_insert_self a s))
        (ih (fun b hb => hf b (mem_insert_of_mem hb)))

private lemma subtype_max_eq {n : ℕ} {I : Type} [DecidableEq I]
    (L : I → Aff n) (s : Finset I) [Nonempty s] (hs : s.Nonempty) (x : E n) :
    (Finset.univ : Finset s).sup' Finset.univ_nonempty (fun i => L i x) =
      s.sup' hs (fun i => L i x) := by
  apply le_antisymm
  · apply Finset.sup'_le _ _
    intro i hi
    exact Finset.le_sup' (fun j => L j x) i.property
  · apply Finset.sup'_le _ _
    intro i hi
    exact Finset.le_sup' (fun j : s => L j x) (mem_univ ⟨i, hi⟩)

private lemma small_affine_max_isHH {n : ℕ} {I : Type} [Fintype I] [Nonempty I]
    (L : I → Aff n) (hcard : Fintype.card I ≤ n + 1) :
    IsHH (fun x => (Finset.univ : Finset I).sup' Finset.univ_nonempty fun i => L i x) := by
  classical
  let e₀ : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let castEmb : Fin (Fintype.card I) ↪ Fin (n + 1) :=
    { toFun := Fin.castLE hcard
      inj' := Fin.castLE_injective hcard }
  let e : I ↪ Fin (n + 1) := e₀.toEmbedding.trans castEmb
  let d : I := Classical.choice (inferInstance : Nonempty I)
  let r : Fin (n + 1) → I := fun j =>
    if hj : ∃ i, e i = j then Classical.choose hj else d
  have hr : Function.Surjective r := by
    intro i
    refine ⟨e i, ?_⟩
    dsimp [r]
    rw [dif_pos (show ∃ k, e k = e i from ⟨i, rfl⟩)]
    apply e.injective
    exact Classical.choose_spec (show ∃ k, e k = e i from ⟨i, rfl⟩)
  let H : E n → ℝ := fun x =>
    (Finset.univ : Finset (Fin (n + 1))).sup' Finset.univ_nonempty fun j => L (r j) x
  have hH : H = fun x =>
      (Finset.univ : Finset I).sup' Finset.univ_nonempty fun i => L i x := by
    funext x
    dsimp [H]
    apply le_antisymm
    · apply Finset.sup'_le _ _
      intro j hj
      exact Finset.le_sup' (fun i => L i x) (mem_univ (r j))
    · apply Finset.sup'_le _ _
      intro i hi
      obtain ⟨j, rfl⟩ := hr i
      exact Finset.le_sup' (fun j => L (r j) x) (mem_univ j)
  have hhinge : IsHinge H := by
    refine ⟨1, fun j => L (r j), Or.inl rfl, ?_⟩
    funext x
    simp [H]
  rw [← hH]
  refine ⟨1, fun _ => H, fun _ => hhinge, ?_⟩
  funext x
  simp

theorem affineMax_isHH_proof {n : ℕ} {I : Type} [Fintype I] [Nonempty I]
    (L : I → Aff n) :
    IsHH (fun x => (Finset.univ : Finset I).sup' Finset.univ_nonempty fun i => L i x) := by
  classical
  have aux : ∀ k : ℕ, ∀ (J : Type) [Fintype J] [Nonempty J],
      Fintype.card J = k → ∀ A : J → Aff n,
        IsHH (fun x => (Finset.univ : Finset J).sup' Finset.univ_nonempty fun j => A j x) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro J fJ nJ hk A
      by_cases hsmall : Fintype.card J ≤ n + 1
      · exact small_affine_max_isHH A hsmall
      · have hlarge : n + 1 < Fintype.card J := lt_of_not_ge hsmall
        obtain ⟨S, T, hS, hT, hSTdisj, hST, hdom⟩ :=
          large_affine_family_partition A hlarge
        let rest : Finset (Finset J) := S.powerset.erase S
        let maxFn : Finset J → E n → ℝ := fun M x =>
          (M ∪ T).sup' (hT.mono subset_union_right) fun j => A j x
        have hproper (M : Finset J) (hM : M ∈ rest) : (M ∪ T).card < k := by
          have hMpow : M ∈ S.powerset := (mem_erase.mp hM).2
          have hMne : M ≠ S := by
            exact fun hEq => (mem_erase.mp hM).1 (hEq ▸ rfl)
          have hMsub : M ⊂ S := Finset.ssubset_iff_subset_ne.mpr
            ⟨mem_powerset.mp hMpow, hMne⟩
          have hsub : M ∪ T ⊂ (Finset.univ : Finset J) := by
            rw [← hST]
            obtain ⟨j, hjS, hjM⟩ := exists_of_ssubset hMsub
            have hjT : j ∉ T := fun hj => (Finset.disjoint_left.mp hSTdisj) hjS hj
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨union_subset_union (Finset.ssubset_iff_subset_ne.mp hMsub).1
              Subset.rfl, ?_⟩
            intro heq
            have hjbig : j ∈ S ∪ T := mem_union_left T hjS
            have hjsmall : j ∈ M ∪ T := by rw [heq]; exact hjbig
            exact (by simpa [hjM, hjT] using hjsmall)
          rw [← hk]
          exact card_lt_card hsub
        have hterm (M : Finset J) (hM : M ∈ rest) : IsHH (maxFn M) := by
          let U : Finset J := M ∪ T
          have hU : U.Nonempty := hT.mono subset_union_right
          letI : Nonempty U := ⟨⟨hT.choose, mem_union_right M hT.choose_spec⟩⟩
          let B : U → Aff n := fun j => A j
          have hUcard : Fintype.card U < k := by
            rw [Fintype.card_coe U]
            exact hproper M hM
          have hrec := ih (Fintype.card U) hUcard U rfl B
          have heq : (fun x => (Finset.univ : Finset U).sup' Finset.univ_nonempty
              fun j => B j x) = maxFn M := by
            funext x
            exact subtype_max_eq A U hU x
          rwa [heq] at hrec
        have hrest : IsHH (∑ M ∈ rest, fun x => (-1 : ℝ) ^ M.card * maxFn M x) := by
          apply isHH_finset_sum
          intro M hM
          exact isHH_signed (hterm M hM)
        have hid := alternating_max_identity A S T hS hT hdom
        have hsigned : IsHH (fun x => (-1 : ℝ) ^ S.card * maxFn S x) := by
          have hnrest := isHH_neg hrest
          rw [show (fun x => (-1 : ℝ) ^ S.card * maxFn S x) =
              -(∑ M ∈ rest, fun x => (-1 : ℝ) ^ M.card * maxFn M x) by
            funext x
            have hx := hid x
            rw [← sum_erase_add _ _ (mem_powerset.mpr (Subset.rfl))] at hx
            simp only [Pi.neg_apply, Finset.sum_apply]
            dsimp [rest, maxFn] at hx ⊢
            linarith]
          exact hnrest
        have htwice := isHH_signed (k := S.card) hsigned
        have hmaxST : maxFn S = fun x =>
            (Finset.univ : Finset J).sup' Finset.univ_nonempty fun j => A j x := by
          funext x
          dsimp [maxFn]
          apply Finset.sup'_congr (hT.mono subset_union_right) hST
          intro j hj
          rfl
        rw [hmaxST] at htwice
        simpa [← mul_assoc, ← mul_pow] using htwice
  exact aux (Fintype.card I) I rfl L


end WangSun

theorem solution {n : ℕ} {I : Type} [Fintype I] [Nonempty I]
    (L : I → ((Fin n → ℝ) →ᵃ[ℝ] ℝ)) :
    IsHH (fun x => (Finset.univ : Finset I).sup' Finset.univ_nonempty fun i => L i x) := by
  exact WangSun.affineMax_isHH_proof L
