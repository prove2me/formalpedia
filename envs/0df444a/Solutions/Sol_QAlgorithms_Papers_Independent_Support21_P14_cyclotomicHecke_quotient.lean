-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P14.cyclotomicHecke_quotient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:15:33.209164+00:00
-- url     : https://prove2.me/submissions/7dbaa9ab-cf81-49e0-adcf-29ff9fd39909

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14
noncomputable section

open scoped BigOperators Classical

open QAlgorithms.Papers.Independent.Support21.P14

section g66i
variable {S : Type*} [CommRing S] {r : ℕ} (P : GroundParameters S r) (n : ℕ)

lemma g66i_heckeE (i : ℕ) :
    RingQuot.mkAlgHom S (HeckeRel P n) (multiplicativeFreeE S n i) = 0 := by
  by_cases hi : i + 1 < n
  · have := RingQuot.mkAlgHom_rel S (HeckeRel.killE (P := P) (n := n) i hi)
    rw [this, map_zero]
  · have : multiplicativeFreeE S n i = 0 := by
      unfold multiplicativeFreeE; rw [dif_neg (by omega)]
    rw [this, map_zero]

def g66i_phi : BMW P n →ₐ[S] MultiplicativeCyclotomicHecke P n :=
  RingQuot.liftAlgHom S ⟨RingQuot.mkAlgHom S (HeckeRel P n), by
    intro a b h
    have hE := g66i_heckeE P n
    cases h with
    | braid h => exact RingQuot.mkAlgHom_rel S (HeckeRel.braid h)
    | skein i hi =>
      have := RingQuot.mkAlgHom_rel S (HeckeRel.skein (P := P) (n := n) i hi)
      rw [this]
      simp only [map_mul, map_sub, map_one, AlgHom.commutes, hE, sub_zero, mul_one]
    | _ => simp only [map_mul, map_pow, AlgHom.commutes, hE, mul_zero, zero_mul, pow_two]⟩

lemma g66i_phi_mk (x : FreeAlgebra S (MultiplicativeBMWLetter n)) :
    g66i_phi P n (RingQuot.mkAlgHom S (MultiplicativeBMWRel P n) x) =
      RingQuot.mkAlgHom S (HeckeRel P n) x := by
  unfold g66i_phi
  rw [RingQuot.liftAlgHom_mkAlgHom_apply]

lemma g66i_J_mul (x : BMW P n) (hx : x ∈ jonesIdeal P n) (a b : BMW P n) :
    a * x * b ∈ jonesIdeal P n := by
  unfold jonesIdeal at hx ⊢
  split_ifs at hx ⊢ with h2
  · induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a', b', rfl⟩ := hz
      exact Submodule.subset_span ⟨a * a', b' * b, by simp only [mul_assoc]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  · rw [Submodule.mem_bot] at hx ⊢; rw [hx]; simp

lemma g66i_E_mem (k : ℕ) (hk : k + 2 ≤ n) : bmwE P n (n - 2 - k) ∈ jonesIdeal P n := by
  induction k with
  | zero =>
    unfold jonesIdeal; rw [if_pos (by omega)]
    exact Submodule.subset_span ⟨1, 1, by simp⟩
  | succ k ih =>
    have ih := ih (by omega)
    have hrel := RingQuot.mkAlgHom_rel S (MultiplicativeBMWRel.tripleE (P := P) (n := n)
      (n - 2 - (k+1)) (n - 2 - k) (by omega) (by omega) (Or.inl (by omega)))
    simp only [map_mul] at hrel
    have : bmwE P n (n - 2 - (k+1)) = bmwE P n (n - 2 - (k+1)) * bmwE P n (n - 2 - k) *
        bmwE P n (n - 2 - (k+1)) := by
      unfold bmwE bmwMap; exact hrel.symm
    rw [this]; exact g66i_J_mul P n _ ih _ _

lemma g66i_E_mem' (i : ℕ) (hi : i + 1 < n) : bmwE P n i ∈ jonesIdeal P n := by
  have := g66i_E_mem P n (n - 2 - i) (by omega)
  rwa [show n - 2 - (n - 2 - i) = i by omega] at this

def g66i_toH : BMWHeckeQuotient P n →ₐ[S] MultiplicativeCyclotomicHecke P n :=
  RingQuot.liftAlgHom S ⟨g66i_phi P n, by
    intro a b h
    rw [← sub_eq_zero, ← map_sub]
    have hker : jonesIdeal P n ≤ LinearMap.ker (g66i_phi P n).toLinearMap := by
      unfold jonesIdeal
      split_ifs
      · rw [Submodule.span_le]
        rintro z ⟨a', b', rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_mul]
        have : g66i_phi P n (bmwE P n (n-2)) = 0 := by
          unfold bmwE bmwMap; rw [g66i_phi_mk, g66i_heckeE]
        rw [this, mul_zero, zero_mul]
      · exact bot_le
    exact hker h⟩

def g66i_toQ : MultiplicativeCyclotomicHecke P n →ₐ[S] BMWHeckeQuotient P n :=
  RingQuot.liftAlgHom S ⟨(RingQuot.mkAlgHom S (fun a b : BMW P n => a - b ∈ jonesIdeal P n)).comp
      (RingQuot.mkAlgHom S (MultiplicativeBMWRel P n)), by
    intro a b h
    have hQ : ∀ x : BMW P n, x ∈ jonesIdeal P n →
        RingQuot.mkAlgHom S (fun a b : BMW P n => a - b ∈ jonesIdeal P n) x = 0 := by
      intro x hx
      rw [← map_zero (RingQuot.mkAlgHom S (fun a b : BMW P n => a - b ∈ jonesIdeal P n))]
      exact RingQuot.mkAlgHom_rel S (by simpa using hx)
    cases h with
    | braid h =>
      simp only [AlgHom.comp_apply]
      rw [RingQuot.mkAlgHom_rel S (MultiplicativeBMWRel.braid h)]
    | killE i hi =>
      simp only [AlgHom.comp_apply, map_zero]
      exact hQ _ (g66i_E_mem' P n i hi)
    | skein i hi =>
      simp only [AlgHom.comp_apply]
      rw [RingQuot.mkAlgHom_rel S (MultiplicativeBMWRel.skein (P := P) (n := n) i hi)]
      have := hQ _ (g66i_E_mem' P n i hi)
      unfold bmwE bmwMap at this
      simp only [map_mul, map_sub, map_one, AlgHom.commutes, this]
      erw [sub_zero, mul_one]⟩

end g66i

theorem solution {S : Type*} [CommRing S] {r : ℕ}
    (P : GroundParameters S r) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (BMWHeckeQuotient P n ≃ₐ[S] MultiplicativeCyclotomicHecke P n) := by
  refine ⟨AlgEquiv.ofAlgHom (g66i_toH P n) (g66i_toQ P n) ?_ ?_⟩
  · apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext x
    simp [g66i_toH, g66i_toQ, RingQuot.liftAlgHom_mkAlgHom_apply, g66i_phi_mk]
  · apply RingQuot.ringQuot_ext'
    apply RingQuot.ringQuot_ext'
    apply FreeAlgebra.hom_ext
    funext x
    simp [g66i_toH, g66i_toQ, RingQuot.liftAlgHom_mkAlgHom_apply, g66i_phi_mk]
