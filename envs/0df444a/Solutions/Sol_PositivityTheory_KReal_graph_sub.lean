-- Prove2me | solution 1 for PositivityTheory.KReal.graph_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:11.618526+00:00
-- url     : https://prove2.me/submissions/11379ae0-803d-4567-96cf-a96e45cf8642

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreCyc
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Theorems.Thm_PositivityTheory_KReal_prodAct_apply
import Theorems.Thm_PI_FJMF_inner_zero_right
import Theorems.Thm_PI_FockOneDegW_Core_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution {p q : ℕ} {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (ρA : Mat p q →ₗ[ℂ] Module.End ℂ A) (ρB : Mat p q →ₗ[ℂ] Module.End ℂ B)
    (hA : IsLie ρA) (hB : IsLie ρB) (aA : AdjG ρA) (aB : AdjG ρB) (lam : Ix p q → ℂ) (x : A) (y : B)
    (hx0 : x ≠ 0)
    (hxK : ∀ a b, sameBlock a b → ρA (Eab a b) x = (if a = b then lam a else 0) • x)
    (hyK : ∀ a b, sameBlock a b → ρB (Eab a b) y = (if a = b then lam a else 0) • y)
    (hxP : ∀ i j, ρA (Eab (.inr j) (.inl i)) x = 0) (hyP : ∀ i j, ρB (Eab (.inr j) (.inl i)) y = 0) :
    ∃ N : Submodule ℂ (A × B), (x, y) ∈ N ∧ (∀ W, ∀ n ∈ N, prodAct ρA ρB W n ∈ N) ∧
      ∀ v, ((0 : A), v) ∈ N → v = 0 := by
  classical
  set P := prodAct ρA ρB with hPdef
  have hP : ∀ Z (n : A × B), P Z n = (ρA Z n.1, ρB Z n.2) := fun Z n => prodAct_apply ρA ρB Z n
  have hLie : ∀ (X Y : Mat p q) (n : A × B), P X (P Y n) = P Y (P X n) + P (X * Y - Y * X) n := by
    intro X Y n
    have h1 := congrArg (fun f => f n.1) (hA X Y)
    have h2 := congrArg (fun f => f n.2) (hB X Y)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1 h2
    refine Prod.ext ?_ ?_
    · simp only [hP, Prod.fst_add]
      rw [← h1]
      abel
    · simp only [hP, Prod.snd_add]
      rw [← h2]
      abel
  have hbr : ∀ a b c d : Ix p q, Eab a b * Eab c d - Eab c d * Eab a b =
      (if b = c then Eab a d else 0) - (if d = a then Eab c b else 0) := by
    intro a b c d
    simp only [Eab]
    split_ifs with h1 h2 h2
    · subst h1
      subst h2
      simp
    · subst h1
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne _ _ _ _ h2]
      simp
    · subst h2
      rw [Matrix.single_mul_single_of_ne _ _ _ _ h1, Matrix.single_mul_single_same]
      simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h1, Matrix.single_mul_single_of_ne _ _ _ _ h2]
  let Rs : Set (Submodule ℂ (A × B)) :=
    {M | (x, y) ∈ M ∧ ∀ (i : Fin p) (j : Fin q), ∀ n ∈ M, P (Eab (.inl i) (.inr j)) n ∈ M}
  let R := sInf Rs
  have hR_xy : (x, y) ∈ R := Submodule.mem_sInf.2 fun M hM => hM.1
  have hR_raise : ∀ (i : Fin p) (j : Fin q), ∀ n ∈ R, P (Eab (.inl i) (.inr j)) n ∈ R :=
    fun i j n hn => Submodule.mem_sInf.2 fun M hM => hM.2 i j n (Submodule.mem_sInf.1 hn M hM)
  have hR_ind : ∀ M : Submodule ℂ (A × B), (x, y) ∈ M →
      (∀ (i : Fin p) (j : Fin q), ∀ n ∈ M, P (Eab (.inl i) (.inr j)) n ∈ M) → R ≤ M :=
    fun M h1 h2 => sInf_le ⟨h1, h2⟩
  have hK : ∀ a b : Ix p q, sameBlock a b → ∀ n ∈ R, P (Eab a b) n ∈ R := by
    let T : Submodule ℂ (A × B) :=
      R ⊓ ⨅ a : Ix p q, ⨅ b : Ix p q, ⨅ (_ : sameBlock a b), R.comap (P (Eab a b))
    have hT : R ≤ T := by
      apply hR_ind
      · refine Submodule.mem_inf.2 ⟨hR_xy, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro a b hab
        rw [hP]
        simp only [hxK a b hab, hyK a b hab]
        rw [← Prod.smul_mk]
        exact R.smul_mem _ hR_xy
      · intro i j n hn
        obtain ⟨hnR, hn2⟩ := Submodule.mem_inf.1 hn
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hn2
        refine Submodule.mem_inf.2 ⟨hR_raise i j n hnR, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro a b hab
        rw [hLie, hbr]
        refine R.add_mem (hR_raise i j _ (hn2 a b hab)) ?_
        rw [map_sub, LinearMap.sub_apply]
        refine R.sub_mem ?_ ?_
        · split_ifs with h
          · subst h
            rcases a with a | a
            · exact hR_raise a j n hnR
            · simp [sameBlock] at hab
          · simp
        · split_ifs with h
          · subst h
            rcases b with b | b
            · simp [sameBlock] at hab
            · exact hR_raise i b n hnR
          · simp
    intro a b hab n hn
    have h := (Submodule.mem_inf.1 (hT hn)).2
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at h
    exact h a b hab
  have hL : ∀ (i : Fin p) (j : Fin q), ∀ n ∈ R, P (Eab (.inr j) (.inl i)) n ∈ R := by
    let T : Submodule ℂ (A × B) :=
      R ⊓ ⨅ i : Fin p, ⨅ j : Fin q, R.comap (P (Eab (.inr j) (.inl i)))
    have hT : R ≤ T := by
      apply hR_ind
      · refine Submodule.mem_inf.2 ⟨hR_xy, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro i j
        rw [hP, hxP, hyP, Prod.mk_zero_zero]
        exact R.zero_mem
      · intro i' j' n hn
        obtain ⟨hnR, hn2⟩ := Submodule.mem_inf.1 hn
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hn2
        refine Submodule.mem_inf.2 ⟨hR_raise i' j' n hnR, ?_⟩
        simp only [Submodule.mem_iInf, Submodule.mem_comap]
        intro i j
        rw [hLie, hbr]
        refine R.add_mem (hR_raise i' j' _ (hn2 i j)) ?_
        rw [map_sub, LinearMap.sub_apply]
        refine R.sub_mem ?_ ?_
        · split_ifs with h
          · exact hK _ _ (by simp [sameBlock]) n hnR
          · simp
        · split_ifs with h
          · exact hK _ _ (by simp [sameBlock]) n hnR
          · simp
    intro i j n hn
    have h := (Submodule.mem_inf.1 (hT hn)).2
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at h
    exact h i j
  have hall : ∀ W, ∀ n ∈ R, P W n ∈ R := by
    intro W n hn
    rw [Matrix.matrix_eq_sum_single W]
    simp only [map_sum, LinearMap.sum_apply]
    refine R.sum_mem fun a _ => R.sum_mem fun b _ => ?_
    have hs : Matrix.single a b (W a b) = W a b • Eab a b := by
      simp [Eab, Matrix.smul_single]
    rw [hs, map_smul, LinearMap.smul_apply]
    refine R.smul_mem _ ?_
    rcases a with a | a <;> rcases b with b | b
    · exact hK _ _ (by simp [sameBlock]) n hn
    · exact hR_raise a b n hn
    · exact hL b a n hn
    · exact hK _ _ (by simp [sameBlock]) n hn
  let Q : Submodule ℂ (A × B) :=
    { carrier := {m | ⟪x, x⟫_ℂ * ⟪m.2, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, x⟫_ℂ}
      add_mem' := by
        intro m m' hm hm'
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, inner_add_left] at hm hm' ⊢
        linear_combination hm + hm'
      zero_mem' := by simp
      smul_mem' := by
        intro c m hm
        simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, inner_smul_left] at hm ⊢
        linear_combination (starRingEnd ℂ c) * hm }
  have hRQ : R ≤ Q := by
    apply hR_ind
    · show ⟪x, x⟫_ℂ * ⟪y, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪x, x⟫_ℂ
      ring
    · intro i j n _
      show ⟪x, x⟫_ℂ * ⟪(P _ n).2, y⟫_ℂ = ⟪y, y⟫_ℂ * ⟪(P _ n).1, x⟫_ℂ
      rw [hP]
      simp only
      rw [aB, hyP, aA, hxP, inner_zero_right, inner_zero_right]
      ring
  let S : Submodule ℂ (A × B) :=
    { carrier := {n | ∀ m ∈ R, ⟪x, x⟫_ℂ * ⟪m.2, n.2⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, n.1⟫_ℂ}
      add_mem' := by
        intro n n' hn hn' m hm
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right]
        linear_combination hn m hm + hn' m hm
      zero_mem' := by
        intro m _
        simp
      smul_mem' := by
        intro c n hn m hm
        simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right]
        linear_combination c * hn m hm }
  have hRS : R ≤ S := by
    apply hR_ind
    · intro m hm
      exact hRQ hm
    · intro i j n hn m hm
      have key := hn (P (Eab (.inr j) (.inl i)) m) (hall _ m hm)
      rw [hP] at key
      simp only at key
      rw [aB, aA] at key
      have he : epsB (Sum.inr j : Ix p q) (Sum.inl i) = -1 := by
        simp [epsB, sameBlock]
      rw [he] at key
      show ⟪x, x⟫_ℂ * ⟪m.2, (P _ n).2⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, (P _ n).1⟫_ℂ
      rw [hP]
      linear_combination -key
  refine ⟨R, hR_xy, hall, ?_⟩
  intro v hv
  have h : ∀ m ∈ R, ⟪x, x⟫_ℂ * ⟪m.2, v⟫_ℂ = ⟪y, y⟫_ℂ * ⟪m.1, (0 : A)⟫_ℂ := hRS hv
  have h0 := h (0, v) hv
  simp only [inner_zero_right, mul_zero] at h0
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx0
  have hvv : ⟪v, v⟫_ℂ = 0 := (mul_eq_zero.1 h0).resolve_left hxx
  exact inner_self_eq_zero.1 hvv
end PositivityTheory.KReal
