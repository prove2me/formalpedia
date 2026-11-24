-- Prove2me | solution 1 for ObjectCentric.submechanisms_distinct_mechanisms_independent
-- status  : ACCEPTED   (prove)
-- author  : @fangshuming
-- created : 2026-11-24T10:03:54.86659+00:00
-- url     : https://prove2.me/submissions/0a78d503-7550-4091-ad2a-0a1edf587234

import Mathlib
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_ObjectCentric_Basic

open MeasureTheory
open ObjectCentric

set_option autoImplicit false

/-- Top-level solution theorem matching the official binders and conclusion. -/
theorem solution {K M N : ℕ} (hM : 0 < M)
    (X : Set (Obs N)) (f : Lat K M → Obs N) (g : Obs N → Lat K M) (hf : IsDiffeoWithInv f g X)
    (hfc : IsCompositional f) (S₁ S₂ : Set (Fin N)) (h₁ : S₁.Nonempty) (h₂ : S₂.Nonempty) :
    ∀ (z : Lat K M) (k : Fin K), S₁ ⊆ indexSet f z k → S₂ ∩ indexSet f z k = ∅ →
      SubmechIndependent f z S₁ S₂ := by
  classical
  intro z k hS1 hkS2
  -- Abbreviations
  let A := jac f z
  -- Key zero patterns on rows:
  have zero_outside_k_of_S1 :
      ∀ ⦃n⦄, n ∈ S₁ → ∀ ⦃j : Fin K⦄, j ≠ k → slotGrad f z n j = 0 := by
    intro n hn j hne
    -- compositionality gives disjoint index sets
    have hd : Disjoint (indexSet f z k) (indexSet f z j) := hfc z k j hne.symm
    have hIn : n ∈ indexSet f z k := hS1 hn
    -- hence n ∉ I_j(z)
    have : n ∉ indexSet f z j := by
      intro hmem
      have : n ∈ (indexSet f z k ∩ indexSet f z j) := ⟨hIn, hmem⟩
      -- contradiction with disjointness
      simpa [Set.disjoint_left, Set.mem_inter_iff] using hd.le_bot this
    -- Therefore the partial gradient is the zero vector
    by_contra hne0
    exact this (by simpa [indexSet] using hne0)
  have zero_k_of_S2 :
      ∀ ⦃n⦄, n ∈ S₂ → slotGrad f z n k = 0 := by
    intro n hn
    -- If it were nonzero, n would lie in S₂ ∩ I_k(z), contradicting emptiness.
    by_contra hne
    have hmem : n ∈ S₂ ∩ indexSet f z k := ⟨hn, by simpa [indexSet] using hne⟩
    have : n ∈ (∅ : Set (Fin N)) := by simpa [hkS2] using hmem
    simpa using this
  -- Row-space based argument
  -- Define the three submatrices
  let A1 : Matrix S₁ (Fin K × Fin M) ℝ := A.submatrix (Subtype.val) id
  let A2 : Matrix S₂ (Fin K × Fin M) ℝ := A.submatrix (Subtype.val) id
  set SU : Set (Fin N) := S₁ ∪ S₂
  let AU : Matrix SU (Fin K × Fin M) ℝ := A.submatrix (Subtype.val) id
  -- Row-span submodules
  let S : Submodule ℝ (Fin K × Fin M → ℝ) := Submodule.span ℝ (Set.range A1.row)
  let T : Submodule ℝ (Fin K × Fin M → ℝ) := Submodule.span ℝ (Set.range A2.row)
  let U : Submodule ℝ (Fin K × Fin M → ℝ) := Submodule.span ℝ (Set.range AU.row)
  -- Show: rows of A1 are supported only on the k-block; rows of A2 vanish on the k-block
  have A1_zero_off_k :
      ∀ r : S₁, ∀ (j : Fin K) (m : Fin M), j ≠ k → A1 r (j, m) = 0 := by
    intro r j m hne
    simpa [A1, slotGrad, A] using congrArg (fun v => v m) (zero_outside_k_of_S1 r.property hne)
  have A2_zero_on_k :
      ∀ r : S₂, ∀ m : Fin M, A2 r (k, m) = 0 := by
    intro r m
    simpa [A2, slotGrad, A] using congrArg (fun v => v m) (zero_k_of_S2 r.property)
  -- Build coordinate submodules: vectors zero off k, and vectors zero on k
  let Wk : Submodule ℝ (Fin K × Fin M → ℝ) :=
    { carrier := {v | ∀ {j : Fin K} {m : Fin M}, j ≠ k → v (j, m) = 0}
    , zero_mem' := by intro j m _; rfl
    , add_mem' := by intro u v hu hv j m hj; simpa [hu hj, hv hj]
    , smul_mem' := by intro a v hv j m hj; simpa [Pi.smul_apply, hv hj] }
  let Wne : Submodule ℝ (Fin K × Fin M → ℝ) :=
    { carrier := {v | ∀ m : Fin M, v (k, m) = 0}
    , zero_mem' := by intro _; rfl
    , add_mem' := by intro u v hu hv m; simpa [hu m, hv m]
    , smul_mem' := by intro a v hv m; simpa [Pi.smul_apply, hv m] }
  -- Wk ∩ Wne ≤ ⊥ (zero on and off the k-block forces zero everywhere)
  have Wk_inf_Wne_le : Wk ⊓ Wne ≤ ⊥ := by
    intro v hv
    have h1 : ∀ m, v (k, m) = 0 := hv.2
    have h2 : ∀ {j} {m}, j ≠ k → v (j, m) = 0 := hv.1
    have : v = 0 := by
      funext c
      rcases c with ⟨j, m⟩
      by_cases hj : j = k
      · subst hj; simpa using h1 m
      · simpa [hj] using h2 hj
    -- membership in ⊥ is by equality to zero
    simpa [Submodule.mem_bot, this]
  -- RowSpace inclusions
  have row_A1_le_Wk : S ≤ Wk := by
    refine Submodule.span_le.mpr ?_
    intro v hv; rcases hv with ⟨r, rfl⟩
    intro j m hj; simpa [Matrix.row] using A1_zero_off_k r j m hj
  have row_A2_le_Wne : T ≤ Wne := by
    refine Submodule.span_le.mpr ?_
    intro v hv; rcases hv with ⟨r, rfl⟩
    intro m; simpa [Matrix.row] using A2_zero_on_k r m
  -- Hence intersection is trivial
  have row_inf_bot : S ⊓ T = ⊥ := by
    apply le_antisymm
    · intro v hv
      have : v ∈ Wk ⊓ Wne := ⟨row_A1_le_Wk hv.1, row_A2_le_Wne hv.2⟩
      exact Wk_inf_Wne_le this
    · exact bot_le
  -- Row space of union equals sup of the two row spaces
  -- Inclusion A1.rowSpace ≤ AU.rowSpace and A2.rowSpace ≤ AU.rowSpace
  have incl1 : S ≤ U := by
    refine Submodule.span_le.mpr ?_
    intro v hv; rcases hv with ⟨r, rfl⟩
    -- map r : S₁ to S := S₁ ∪ S₂
    have hrow :
        Matrix.row AU ⟨(r : Fin N), by
          have : (r : Fin N) ∈ SU := by
            change (r : Fin N) ∈ S₁ ∪ S₂
            exact Or.inl r.property
          simpa [SU] using this⟩
        = Matrix.row A1 r := by
      -- both sides reduce to (fun c => A (r : Fin N) c)
      rfl
    exact hrow ▸
      Submodule.subset_span ⟨⟨(r : Fin N), by
        have : (r : Fin N) ∈ SU := by
          change (r : Fin N) ∈ S₁ ∪ S₂
          exact Or.inl r.property
        simpa [SU] using this⟩, rfl⟩
  have incl2 : T ≤ U := by
    refine Submodule.span_le.mpr ?_
    intro v hv; rcases hv with ⟨r, rfl⟩
    have hrow :
        Matrix.row AU ⟨(r : Fin N), by
          have : (r : Fin N) ∈ SU := by
            change (r : Fin N) ∈ S₁ ∪ S₂
            exact Or.inr r.property
          simpa [SU] using this⟩
        = Matrix.row A2 r := by
      rfl
    exact hrow ▸
      Submodule.subset_span ⟨⟨(r : Fin N), by
        have : (r : Fin N) ∈ SU := by
          change (r : Fin N) ∈ S₁ ∪ S₂
          exact Or.inr r.property
        simpa [SU] using this⟩, rfl⟩
  have AU_row_eq_sup : U = S ⊔ T := by
    apply le_antisymm
    · -- AU.rowSpace ≤ sup
      refine Submodule.span_le.mpr ?_
      intro v hv; rcases hv with ⟨r, rfl⟩
      rcases r with ⟨n, hn⟩
      have hn' : n ∈ S₁ ∪ S₂ := by simpa [SU] using hn
      cases hn' with
      | inl h1 =>
          -- show the AU-row generator equals the corresponding A1-row
          have hrow :
              Matrix.row AU ⟨n, hn⟩ = Matrix.row A1 ⟨n, h1⟩ := by
            -- compare as functions and use row_def
            have : AU ⟨n, hn⟩ = A1 ⟨n, h1⟩ := by
              funext c; rfl
            simpa [Matrix.row_def] using this
          have hm : Matrix.row A1 ⟨n, h1⟩ ∈ S :=
            Submodule.subset_span ⟨⟨n, h1⟩, rfl⟩
          -- lift to the sup via `le_sup_left`
          have hmSup :
              Matrix.row A1 ⟨n, h1⟩ ∈ S ⊔ T :=
            (show S ≤ S ⊔ T from le_sup_left) hm
          -- transport membership through `hrow`
          simpa [hrow]
            using hmSup
      | inr h2 =>
          have hrow :
              Matrix.row AU ⟨n, hn⟩ = Matrix.row A2 ⟨n, h2⟩ := by
            have : AU ⟨n, hn⟩ = A2 ⟨n, h2⟩ := by
              funext c; rfl
            simpa [Matrix.row_def] using this
          have hm : Matrix.row A2 ⟨n, h2⟩ ∈ T :=
            Submodule.subset_span ⟨⟨n, h2⟩, rfl⟩
          have hmSup : Matrix.row A2 ⟨n, h2⟩ ∈ S ⊔ T :=
            (show T ≤ S ⊔ T from le_sup_right) hm
          simpa [hrow]
            using hmSup
    · -- sup ≤ AU.rowSpace
      -- using lattice fact: a ⊔ b ≤ c if a ≤ c and b ≤ c
      -- here a=rowSpan A1, b=rowSpan A2, c=rowSpan AU
      have hle : S ≤ U ∧ T ≤ U :=
        ⟨incl1, incl2⟩
      exact sup_le hle.1 hle.2
  -- Convert ranks to finranks of row spaces and finish using finrank_sup with trivial inf
  have h_rank_A1 : A1.rank = Module.finrank ℝ S := by
    simpa using (Matrix.rank_eq_finrank_span_row (R:=ℝ) (A:=A1))
  have h_rank_A2 : A2.rank = Module.finrank ℝ T := by
    simpa using (Matrix.rank_eq_finrank_span_row (R:=ℝ) (A:=A2))
  have h_rank_AU : AU.rank = Module.finrank ℝ U := by
    simpa using (Matrix.rank_eq_finrank_span_row (R:=ℝ) (A:=AU))
  -- Rank(sup) + Rank(inf) = Rank(s) + Rank(t); convert ranks to finranks
  -- Use finrank version directly with finite-dimensionality of spans of finite sets
  -- S, T are spans of finite ranges since S₁, S₂ are subtypes of `Fin N`
  have hSfin : (Set.range A1.row).Finite := Set.finite_range _
  have hTfin : (Set.range A2.row).Finite := Set.finite_range _
  have hUfin : (Set.range AU.row).Finite := Set.finite_range _
  -- Install instances only for this call
  letI : FiniteDimensional ℝ S := by
    simpa [S] using (FiniteDimensional.span_of_finite (K:=ℝ) hSfin)
  letI : FiniteDimensional ℝ T := by
    simpa [T] using (FiniteDimensional.span_of_finite (K:=ℝ) hTfin)
  -- First, get the equality for `S ⊔ T`
  have finrank_sup_eq_ST :
      Module.finrank ℝ ↥(S ⊔ T) + Module.finrank ℝ ↥(S ⊓ T)
        = Module.finrank ℝ ↥S + Module.finrank ℝ ↥T :=
    (Submodule.finrank_sup_add_finrank_inf_eq (K:=ℝ) (s:=S) (t:=T))
  -- Transport to `U` using `U = S ⊔ T` at the type level
  have finrank_U_rewrite :
      Module.finrank ℝ ↥U = Module.finrank ℝ ↥(S ⊔ T) := by
    simpa using
      congrArg (fun P : Submodule ℝ (Fin K × Fin M → ℝ) => Module.finrank ℝ ↥P) AU_row_eq_sup
  have finrank_sup_eq :
      Module.finrank ℝ ↥U + Module.finrank ℝ ↥(S ⊓ T)
        = Module.finrank ℝ ↥S + Module.finrank ℝ ↥T := by
    simpa [finrank_U_rewrite] using finrank_sup_eq_ST
  have inf_finrank_zero : Module.finrank ℝ ↥(S ⊓ T) = 0 := by
    -- transport finrank across equality (S ⊓ T) = ⊥
    have hb : Module.finrank ℝ ↥(⊥ : Submodule ℝ (Fin K × Fin M → ℝ)) = 0 :=
      finrank_bot (R:=ℝ) (M:=Fin K × Fin M → ℝ)
    have hrewrite :
        Module.finrank ℝ ↥(S ⊓ T) = Module.finrank ℝ ↥(⊥ : Submodule ℝ (Fin K × Fin M → ℝ)) := by
      simpa using
        congrArg (fun P : Submodule ℝ (Fin K × Fin M → ℝ) => Module.finrank ℝ ↥P) row_inf_bot
    simpa [hrewrite] using hb
  have finrank_sup :
      Module.finrank ℝ ↥U = Module.finrank ℝ ↥S + Module.finrank ℝ ↥T := by
    have hsum := finrank_sup_eq
    simpa [inf_finrank_zero, add_comm, add_left_comm, add_assoc] using hsum
  -- Combine equalities
  have : AU.rank = A1.rank + A2.rank := by
    simpa [h_rank_A1, h_rank_A2, h_rank_AU] using finrank_sup
  -- Unfold `subRank` and conclude
  simpa [SubmechIndependent, subRank, AU, A1, A2] using this
