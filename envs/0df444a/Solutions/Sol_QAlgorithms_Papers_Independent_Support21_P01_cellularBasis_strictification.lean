-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P01.cellularBasis_strictification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:26:44.222134+00:00
-- url     : https://prove2.me/submissions/6be370f9-5378-4d4a-9ab7-444040f01acc

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P01
noncomputable section

open scoped TensorProduct

open QAlgorithms.Papers.Independent.Support21.P01

open QAlgorithms.Papers.Independent.Renew46.P16



/-- Remark 2.4(2), PDF p.5: when 2 is invertible, the explicit adjustment
is a cellular basis with exact index swapping, on the same label poset and
index sets. Finite labels and finite cell indices follow the finite-cell
interpretation used in the source's cell-chain arguments. Empty cell index
sets are allowed; the input basis has only the relaxed axiom. -/
theorem solution
    {R A L : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A]
    [PartialOrder L] [Finite L]
    {T : L → Type*} [∀ l, Fintype (T l)]
    (c : CellIndex L T → A) (i : A →ₗ[R] A)
    (hcell : IsWeakCellularBasis (R := R) c i)
    (half : R) (hhalf : (2 : R) * half = 1) :
    IsWeakCellularBasis (R := R) (strictifiedCellBasis c i half) i ∧
      ∀ (l : L) (s t : T l),
        i (strictifiedCellBasis c i half ⟨l, (s, t)⟩) =
          strictifiedCellBasis c i half ⟨l, (t, s)⟩ := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  obtain ⟨hinv, hanti, hli, hsp, hmulc, hswap⟩ := hcell
  set c' := strictifiedCellBasis c i half with hc'
  -- monotonicity of the higher spans, for any family
  have hmono : ∀ (d : CellIndex L T → A) (l m : L), l < m →
      higherCellSpan (R := R) d m ≤ higherCellSpan (R := R) d l := by
    intro d l m hlm
    apply Submodule.span_le.2
    rintro _ ⟨m', hm', s, t, rfl⟩
    exact Submodule.subset_span ⟨m', hlm.trans hm', s, t, rfl⟩
  have hdiff : ∀ (l : L) (s t : T l), c' ⟨l, (s, t)⟩ - c ⟨l, (s, t)⟩ ∈ higherCellSpan (R := R) c l := by
    intro l s t
    have : c' ⟨l, (s, t)⟩ - c ⟨l, (s, t)⟩ = half • (i (c ⟨l, (t, s)⟩) - c ⟨l, (s, t)⟩) := by
      simp [hc', strictifiedCellBasis]
    rw [this]
    exact Submodule.smul_mem _ _ (hswap l t s)
  have hle1 : ∀ l, higherCellSpan (R := R) c' l ≤ higherCellSpan (R := R) c l := by
    intro l
    apply Submodule.span_le.2
    rintro _ ⟨m, hm, s, t, rfl⟩
    have h1 : c ⟨m, (s, t)⟩ ∈ higherCellSpan (R := R) c l := Submodule.subset_span ⟨m, hm, s, t, rfl⟩
    have h2 := hmono c l m hm (hdiff m s t)
    have := Submodule.add_mem _ h1 h2
    simpa using this
  have hle2 : ∀ l, higherCellSpan (R := R) c l ≤ higherCellSpan (R := R) c' l := by
    intro l
    induction l using WellFoundedGT.induction with
    | _ l ih =>
      apply Submodule.span_le.2
      rintro _ ⟨m, hm, s, t, rfl⟩
      have h1 : c' ⟨m, (s, t)⟩ ∈ higherCellSpan (R := R) c' l := Submodule.subset_span ⟨m, hm, s, t, rfl⟩
      have h2 := hmono c' l m hm (ih m hm (hdiff m s t))
      have := Submodule.sub_mem _ h1 h2
      simpa using this
  have hH : ∀ l, higherCellSpan (R := R) c' l = higherCellSpan (R := R) c l :=
    fun l => le_antisymm (hle1 l) (hle2 l)
  have hideal : ∀ (l : L) (a x : A), x ∈ higherCellSpan (R := R) c l →
      a * x ∈ higherCellSpan (R := R) c l := by
    intro l a x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, s, t, rfl⟩ := hx
      obtain ⟨r, hr⟩ := hmulc m s a
      have h1 := hmono c l m hm (hr t)
      have h2 : ∑ v : T m, r v • c ⟨m, (v, t)⟩ ∈ higherCellSpan (R := R) c l :=
        Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hm, v, t, rfl⟩)
      have := Submodule.add_mem _ h1 h2
      simpa using this
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx
  -- spanning
  have hsp' : Submodule.span R (Set.range c') = ⊤ := by
    rw [eq_top_iff, ← hsp]
    apply Submodule.span_le.2
    rintro _ ⟨⟨l, s, t⟩, rfl⟩
    have h1 : c' ⟨l, (s, t)⟩ ∈ Submodule.span R (Set.range c') := Submodule.subset_span ⟨_, rfl⟩
    have h2 : c' ⟨l, (s, t)⟩ - c ⟨l, (s, t)⟩ ∈ Submodule.span R (Set.range c') := by
      have := hle2 l (hdiff l s t)
      refine (Submodule.span_le.2 ?_) this
      rintro _ ⟨m, _, s', t', rfl⟩
      exact Submodule.subset_span ⟨_, rfl⟩
    have := Submodule.sub_mem _ h1 h2
    simpa using this
  -- linear independence
  have hli' : LinearIndependent R c' := by
    let Bc : Module.Basis (CellIndex L T) R A := Module.Basis.mk hli (by rw [hsp])
    haveI : Module.Finite R A := Module.Finite.of_basis Bc
    rw [linearIndependent_iff_injective_fintypeLinearCombination]
    let g := Bc.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R c'
    have hsurj : Function.Surjective (Fintype.linearCombination R c') := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp']
    have hg : Function.Surjective g := Bc.equivFun.surjective.comp hsurj
    have hginj := OrzechProperty.injective_of_surjective_endomorphism g hg
    intro x y hxy
    exact hginj (by simp [g, hxy])
  have hstrict : ∀ (l : L) (s t : T l), i (c' ⟨l, (s, t)⟩) = c' ⟨l, (t, s)⟩ := by
    intro l s t
    simp only [hc', strictifiedCellBasis, map_add, map_smul, map_sub]
    rw [hinv]
    linear_combination (norm := module) (-hhalf) • (i (c ⟨l, (s, t)⟩) - c ⟨l, (t, s)⟩)
  refine ⟨⟨hinv, hanti, hli', hsp', ?_, ?_⟩, hstrict⟩
  · intro l s a
    obtain ⟨r, hr⟩ := hmulc l s a
    refine ⟨r, fun t => ?_⟩
    rw [hH]
    have e : a * c' ⟨l, (s, t)⟩ - ∑ v : T l, r v • c' ⟨l, (v, t)⟩ =
        (a * c ⟨l, (s, t)⟩ - ∑ v : T l, r v • c ⟨l, (v, t)⟩) +
        (a * (c' ⟨l, (s, t)⟩ - c ⟨l, (s, t)⟩) -
          ∑ v : T l, r v • (c' ⟨l, (v, t)⟩ - c ⟨l, (v, t)⟩)) := by
      simp only [mul_sub, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e]
    refine Submodule.add_mem _ (hr t) (Submodule.sub_mem _ (hideal l a _ (hdiff l s t)) ?_)
    exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (hdiff l v t)
  · intro l s t
    rw [hstrict, sub_self]
    exact Submodule.zero_mem _


end
