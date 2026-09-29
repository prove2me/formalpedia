-- Prove2me | solution 1 for Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/b5fce22b-4fb3-528d-86c7-2b0b721c04f8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation

set_option Elab.async false

set_option autoImplicit false

noncomputable section

p2m_open "Matrix P2MW.S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation.Matrix"

namespace Module
p2m_export "Module" "support End.mul_eq_comp finrank compHom End.mul_apply mk Finite.of_restrictScalars_finite End restrictScalars finrank_matrix End.exists_eigenvalue End.one_apply End.mem_eigenspace_iff"
namespace End
p2m_export "Module.End" "mul_eq_comp mul_apply eigenspace exists_eigenvalue one_apply mem_eigenspace_iff"
p2m_open "Module.End Module"

private theorem exists_common_eigenvector_of_commute {k : Type} [Field k] [IsAlgClosed k] {ι : Type}
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]
    (f : ι → Module.End k W) (hc : ∀ i j, Commute (f i) (f j)) :
    ∃ v : W, v ≠ 0 ∧ ∀ i, ∃ μ : k, f i v = μ • v := by
  suffices key : ∀ (n : ℕ) {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
      (f : ι → Module.End k V), (∀ i j, Commute (f i) (f j)) → Module.finrank k V = n →
      ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : k, f i v = μ • v from key _ f hc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ _ f hc hn
    by_cases hsc : ∀ i, ∃ μ : k, ∀ v : V, f i v = μ • v
    · obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact ⟨v, hv, fun i => (hsc i).imp fun μ h => h v⟩
    · push Not at hsc
      obtain ⟨i₀, hi₀⟩ := hsc
      obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue (f i₀)
      have hEbot : (f i₀).eigenspace μ₀ ≠ ⊥ := hμ₀
      have hEtop : (f i₀).eigenspace μ₀ ≠ ⊤ := by
        intro htop
        obtain ⟨v, hv⟩ := hi₀ μ₀
        exact hv (Module.End.mem_eigenspace_iff.mp (htop ▸ Submodule.mem_top))
      have hmaps : ∀ j, Set.MapsTo (f j) ((f i₀).eigenspace μ₀) ((f i₀).eigenspace μ₀) := by
        intro j v hv
        rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv ⊢
        have hcomm : f i₀ (f j v) = f j (f i₀ v) := by
          rw [← Module.End.mul_apply, (hc i₀ j).eq, Module.End.mul_apply]
        rw [hcomm, hv, map_smul]
      haveI : Nontrivial ((f i₀).eigenspace μ₀) := Submodule.nontrivial_iff_ne_bot.mpr hEbot
      have hlt : Module.finrank k ((f i₀).eigenspace μ₀) < n := hn ▸ Submodule.finrank_lt hEtop
      obtain ⟨w, hw0, hw⟩ := ih _ hlt (fun j => (f j).restrict (hmaps j))
        (fun i j => LinearMap.restrict_commute (hc i j) _ _) rfl
      refine ⟨(w : V), fun h => hw0 ((Submodule.coe_eq_zero).mp h), fun i => ?_⟩
      obtain ⟨μ, hμ⟩ := hw i
      refine ⟨μ, ?_⟩
      have := congrArg Subtype.val hμ
      simpa only [LinearMap.coe_restrict_apply, Submodule.coe_smul] using this

end Module.End

namespace Matrix
p2m_export "Matrix" "det_smul trace_sub fromBlocks_add ext fromBlocks_inj row sub_apply traceLinearMap smul_single fromBlocks_smul trace_smul zero map_single det_one diag scalar comp trace_mul_cycle fromBlocks_multiply charpoly trace_mul_comm toLin'_one det_fin_two Nondegenerate toLin'_mul trace_add trace_single_eq_same fromBlocks rank matrix_eq_sum_single det_mul trace_sum zero_apply of_apply single one_apply smul_apply det fromBlocks_zero smul_eq_mulVec add_apply comp_apply of smul_mul trace_zero map toLin' fromBlocks_one one mul_apply trace trace_mul_single module trace_fin_two mulVec SeparatingLeft"
p2m_open "Matrix"

open LinearMap (BilinForm)

section DetPolar

variable {k : Type} [Field k]

local notation3 "M2" => Matrix (Fin 2) (Fin 2) k

private def detPolar : BilinForm k M2 :=
  LinearMap.mk₂ k (fun X Y => X.trace * Y.trace - (X * Y).trace)
    (fun X₁ X₂ Y => by simp only [trace_add, add_mul]; ring)
    (fun c X Y => by simp only [trace_smul, smul_eq_mul, Matrix.smul_mul]; ring)
    (fun X Y₁ Y₂ => by simp only [trace_add, mul_add]; ring)
    (fun c X Y => by simp only [trace_smul, smul_eq_mul, Matrix.mul_smul]; ring)

private lemma detPolar_apply (X Y : M2) :
    detPolar X Y = X.trace * Y.trace - (X * Y).trace := rfl

private lemma detPolar_symm (X Y : M2) : detPolar X Y = detPolar Y X := by
  rw [detPolar_apply, detPolar_apply, mul_comm X.trace, Matrix.trace_mul_comm]

private lemma det_add_eq (X Y : M2) :
    (X + Y).det = X.det + Y.det + detPolar X Y := by
  simp only [Matrix.det_fin_two, detPolar_apply, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.add_apply]
  ring

private lemma detPolar_nondeg : (detPolar (k := k)).Nondegenerate := by
  have sepL : (detPolar (k := k)).SeparatingLeft := by
    intro X hX

    have key : ∀ a b : Fin 2,
        X.trace * (Matrix.single a b (1:k)).trace - X b a = 0 := fun a b => by
      have h := hX (Matrix.single a b (1:k))
      rwa [detPolar_apply, Matrix.trace_mul_single, MulOpposite.op_one, one_smul] at h
    have h00 := key 0 0; have h01 := key 0 1; have h10 := key 1 0; have h11 := key 1 1
    rw [Matrix.trace_single_eq_same, mul_one, Matrix.trace_fin_two] at h00 h11
    rw [show (Matrix.single (0:Fin 2) 1 (1:k)).trace = 0 by simp,
        mul_zero, zero_sub, neg_eq_zero] at h01
    rw [show (Matrix.single (1:Fin 2) 0 (1:k)).trace = 0 by simp,
        mul_zero, zero_sub, neg_eq_zero] at h10

    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply]
    · show X 0 0 = 0; linear_combination h11
    · exact h10
    · exact h01
    · show X 1 1 = 0; linear_combination h00
  exact ⟨sepL, fun Y hY => sepL Y fun X => (detPolar_symm Y X) ▸ hY X⟩

private lemma sq_eq_trace_smul_sub_det_smul_one_aux (N : M2) :
    N ^ 2 = N.trace • N - N.det • (1 : M2) := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

end DetPolar

private theorem spanTop_det_sub_one_eq_zero_isFalse
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (hone : ∀ g : G, (ρ g - 1).det = 0) :
    False := by
  set N : G → Matrix (Fin 2) (Fin 2) k := fun g => ρ g - 1 with hNdef
  have hdetN : ∀ g, (N g).det = 0 := hone

  have hNmul : ∀ g h, N (g * h) = N g * N h + N g + N h := fun g h => by
    simp only [hNdef, map_mul]; noncomm_ring

  have hNsq : ∀ g, N g ^ 2 = (N g).trace • N g := fun g => by
    rw [sq_eq_trace_smul_sub_det_smul_one_aux, hone g, zero_smul, sub_zero]

  have hΦNN : ∀ g h, detPolar (N g) (N h) = 0 := by
    intro g h

    have key1 : detPolar (N g * N h) (N g) = 0 := by
      have cyc : (N g * N h * N g).trace = (N g).trace * (N g * N h).trace := by
        rw [Matrix.trace_mul_cycle, ← pow_two, hNsq g, Matrix.smul_mul, trace_smul,
          smul_eq_mul]
      rw [detPolar_apply, cyc]; ring
    have key2 : detPolar (N g * N h) (N h) = 0 := by
      have cyc : (N g * N h * N h).trace = (N h).trace * (N g * N h).trace := by
        rw [mul_assoc, ← pow_two, hNsq h, Matrix.mul_smul, trace_smul, smul_eq_mul]
      rw [detPolar_apply, cyc]; ring

    have expand : (0:k) = detPolar (N g * N h) (N g) + detPolar (N g * N h) (N h)
        + detPolar (N g) (N h) := by
      have hd : (N (g*h)).det = (N g * N h + N g + N h).det := by rw [hNmul]
      rw [hdetN (g*h), det_add_eq (N g * N h + N g) (N h), det_add_eq (N g * N h) (N g),
        Matrix.det_mul, hdetN g, zero_mul, hdetN h, map_add, LinearMap.add_apply] at hd

      linear_combination hd
    linear_combination -expand - key1 - key2

  set S : Submodule k (Matrix (Fin 2) (Fin 2) k) := Submodule.span k (Set.range N) with hSdef
  have hSiso : ∀ X ∈ S, ∀ Y ∈ S, detPolar X Y = 0 := by
    intro X hX Y hY
    refine Submodule.span_induction (p := fun X _ => detPolar X Y = 0) ?_ ?_ ?_ ?_ hX
    · rintro _ ⟨g, rfl⟩
      refine Submodule.span_induction (p := fun Y _ => detPolar (N g) Y = 0) ?_ ?_ ?_ ?_ hY
      · rintro _ ⟨h, rfl⟩; exact hΦNN g h
      · simp
      · intro Y₁ Y₂ _ _ h1 h2; simp [map_add, h1, h2]
      · intro c Y₁ _ h1; simp [map_smul, h1]
    · simp
    · intro X₁ X₂ _ _ h1 h2; simp only [map_add, LinearMap.add_apply, h1, h2, add_zero]
    · intro c X₁ _ h1; simp only [map_smul, LinearMap.smul_apply, h1, smul_zero]
  have hSorth : S ≤ detPolar.orthogonal S := fun X hX Y hY => hSiso Y hY X hX

  have hS1 : S ⊔ Submodule.span k {(1 : Matrix (Fin 2) (Fin 2) k)} = ⊤ := by
    rw [eq_top_iff, ← hirr]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g, rfl⟩
    refine Submodule.mem_sup.mpr ⟨N g, Submodule.subset_span ⟨g, rfl⟩, 1,
      Submodule.subset_span rfl, ?_⟩
    simp [hNdef]
  have hrank4 : Module.finrank k (Matrix (Fin 2) (Fin 2) k) = 4 := by
    simp [Module.finrank_matrix]
  have hS_ge3 : 3 ≤ Module.finrank k S := by
    have hone_ne : (1 : Matrix (Fin 2) (Fin 2) k) ≠ 0 := one_ne_zero
    have h4 : Module.finrank k (Matrix (Fin 2) (Fin 2) k) ≤ Module.finrank k S + 1 := by
      calc Module.finrank k (Matrix (Fin 2) (Fin 2) k)
          = Module.finrank k (⊤ : Submodule k (Matrix (Fin 2) (Fin 2) k)) := (finrank_top k _).symm
        _ = Module.finrank k ↑(S ⊔ Submodule.span k {(1:Matrix (Fin 2) (Fin 2) k)}) := by rw [hS1]
        _ ≤ Module.finrank k S
              + Module.finrank k (Submodule.span k {(1:Matrix (Fin 2) (Fin 2) k)}) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ = Module.finrank k S + 1 := by rw [finrank_span_singleton hone_ne]
    omega

  have hS_le2 : Module.finrank k S ≤ 2 := by
    have hperp : Module.finrank k (detPolar.orthogonal S)
        = Module.finrank k (Matrix (Fin 2) (Fin 2) k) - Module.finrank k S :=
      LinearMap.BilinForm.finrank_orthogonal detPolar_nondeg S
    have hle : Module.finrank k S ≤ Module.finrank k (detPolar.orthogonal S) :=
      Submodule.finrank_mono hSorth
    omega
  omega

end Matrix

namespace Representation
p2m_export "Representation" "free quotient"
p2m_open "Representation"

private theorem commuting_hann_spanTop_isFalse_of_isAlgClosed
    {k : Type} [Field k] [IsAlgClosed k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]
    (σW : Representation k G W)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (hcomm : ∀ g h : G, Commute (σW g : W →ₗ[k] W) (σW h)) :
    False := by
  classical

  obtain ⟨v, hv0, hv⟩ :=
    Module.End.exists_common_eigenvector_of_commute (fun g : G => (σW g : W →ₗ[k] W)) hcomm
  choose lam hlam using hv

  have hquad : ∀ g, lam g ^ 2 - (ρ g).trace * lam g + (ρ g).det = 0 := by
    intro g
    have h := LinearMap.congr_fun (hann g) v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
      Module.End.one_apply, pow_two, Module.End.mul_apply, hlam, map_smul, smul_smul] at h
    rw [← sub_smul, ← add_smul, smul_eq_zero] at h
    rcases h with h | h
    · linear_combination h
    · exact absurd h hv0
  have hdet : ∀ g, (ρ g).det ≠ 0 := by
    intro g h0
    have h1 : (ρ g).det * (ρ g⁻¹).det = 1 := by
      rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hlam0 : ∀ g, lam g ≠ 0 := by
    intro g h0
    apply hdet g
    have := hquad g
    rw [h0] at this
    simpa using this
  have hmul : ∀ g h, lam (g * h) = lam g * lam h := by
    intro g h
    have e1 : σW (g * h) v = lam (g * h) • v := hlam _
    rw [map_mul, Module.End.mul_apply, hlam h, map_smul, hlam g, smul_smul, mul_comm] at e1
    exact (smul_left_injective k hv0 e1).symm
  have hone1 : lam 1 = 1 := by
    have e1 : σW 1 v = lam 1 • v := hlam 1
    rw [map_one, Module.End.one_apply] at e1
    have e2 : (1 : k) • v = lam 1 • v := by rw [one_smul]; exact e1
    exact (smul_left_injective k hv0 e2).symm

  let ρ' : G →* Matrix (Fin 2) (Fin 2) k :=
    { toFun := fun g => (lam g)⁻¹ • ρ g
      map_one' := by rw [map_one, hone1, inv_one, one_smul]
      map_mul' := fun g h => by rw [map_mul, hmul, mul_inv, smul_mul_smul_comm] }
  have hρ' : ∀ g, ρ' g = (lam g)⁻¹ • ρ g := fun g => rfl
  have hirr' : Submodule.span k (Set.range (fun g : G => ρ' g)) = ⊤ := by
    rw [eq_top_iff, ← hirr, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    have hg : ρ g = lam g • ρ' g := by rw [hρ', smul_smul, mul_inv_cancel₀ (hlam0 g), one_smul]
    show ρ g ∈ _
    rw [hg]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
  have hone : ∀ g : G, (ρ' g - 1).det = 0 := by
    intro g
    have key : (ρ g - lam g • (1 : Matrix (Fin 2) (Fin 2) k)).det =
        lam g ^ 2 - (ρ g).trace * lam g + (ρ g).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
      simp
      ring
    have hsub : ρ' g - 1 = (lam g)⁻¹ • (ρ g - lam g • (1 : Matrix (Fin 2) (Fin 2) k)) := by
      rw [hρ', smul_sub, smul_smul, inv_mul_cancel₀ (hlam0 g), one_smul]
    rw [hsub, Matrix.det_smul, key, hquad, mul_zero]
  exact Matrix.spanTop_det_sub_one_eq_zero_isFalse ρ' hirr' hone

private theorem commuting_hann_spanTop_isFalse
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Nontrivial W]
    (σW : Representation k G W)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (hcomm : ∀ g h : G, Commute (σW g : W →ₗ[k] W) (σW h)) :
    False := by
  classical

  let ρK : G →* Matrix (Fin 2) (Fin 2) (AlgebraicClosure k) :=
    (algebraMap k (AlgebraicClosure k)).mapMatrix.toMonoidHom.comp ρ
  have hρK : ∀ g, ρK g = (ρ g).map (algebraMap k (AlgebraicClosure k)) := fun g => rfl

  have hirrK : Submodule.span (AlgebraicClosure k) (Set.range (fun g : G => ρK g)) = ⊤ := by
    let φ : Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) (AlgebraicClosure k) :=
      (Algebra.linearMap k (AlgebraicClosure k)).mapMatrix
    have hφ : ∀ X, φ X = X.map (algebraMap k (AlgebraicClosure k)) := fun X => rfl
    have hmem : ∀ X : Matrix (Fin 2) (Fin 2) k,
        X.map (algebraMap k (AlgebraicClosure k)) ∈
          Submodule.span (AlgebraicClosure k) (Set.range (fun g : G => ρK g)) := by
      intro X
      have hX : X ∈ Submodule.span k (Set.range (fun g : G => ρ g)) := by rw [hirr]; exact Submodule.mem_top
      have h1 : φ X ∈ Submodule.span k (φ '' Set.range (fun g : G => ρ g)) := by
        rw [← Submodule.map_span]; exact Submodule.mem_map_of_mem hX
      have h2 : φ '' Set.range (fun g : G => ρ g) = Set.range (fun g : G => ρK g) := by
        rw [← Set.range_comp]; rfl
      rw [h2] at h1
      exact Submodule.span_le_restrictScalars k (AlgebraicClosure k) _ h1
    rw [eq_top_iff]
    rintro Y -
    rw [Matrix.matrix_eq_sum_single Y]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
    have hs : Matrix.single i j (Y i j) =
        Y i j • (Matrix.single i j (1 : k)).map (algebraMap k (AlgebraicClosure k)) := by
      rw [Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs]
    exact Submodule.smul_mem _ _ (hmem _)

  let σ' : Representation (AlgebraicClosure k) G (TensorProduct k (AlgebraicClosure k) W) :=
    { toFun := fun g => (σW g).baseChange (AlgebraicClosure k)
      map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.baseChange_mul _ _ }
  have hσ' : ∀ g, σ' g = (σW g).baseChange (AlgebraicClosure k) := fun g => rfl
  have htr : ∀ g, (ρK g).trace = algebraMap k (AlgebraicClosure k) (ρ g).trace := fun g =>
    (AddMonoidHom.map_trace (algebraMap k (AlgebraicClosure k)) (ρ g)).symm
  have hdet : ∀ g, (ρK g).det = algebraMap k (AlgebraicClosure k) (ρ g).det := fun g =>
    (RingHom.map_det (algebraMap k (AlgebraicClosure k)) (ρ g)).symm
  have hann' : ∀ g : G, σ' g ^ 2 - Matrix.trace (ρK g) • σ' g +
      (ρK g).det • (1 : TensorProduct k (AlgebraicClosure k) W →ₗ[AlgebraicClosure k]
        TensorProduct k (AlgebraicClosure k) W) = 0 := by
    intro g
    have h := congrArg (fun T : W →ₗ[k] W => T.baseChange (AlgebraicClosure k)) (hann g)
    simp only [LinearMap.baseChange_zero, LinearMap.baseChange_add, LinearMap.baseChange_sub,
      LinearMap.baseChange_pow, LinearMap.baseChange_smul, LinearMap.baseChange_one] at h
    rw [htr, hdet, hσ', algebraMap_smul, algebraMap_smul]
    exact h
  have hcomm' : ∀ g h : G, Commute (σ' g : TensorProduct k (AlgebraicClosure k) W →ₗ[AlgebraicClosure k]
      TensorProduct k (AlgebraicClosure k) W) (σ' h) := by
    intro g h
    show σ' g * σ' h = σ' h * σ' g
    rw [hσ', hσ', ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (hcomm g h).eq]

  haveI : Nontrivial (TensorProduct k (AlgebraicClosure k) W) := inferInstance
  haveI : FiniteDimensional (AlgebraicClosure k) (TensorProduct k (AlgebraicClosure k) W) := inferInstance
  exact commuting_hann_spanTop_isFalse_of_isAlgClosed ρK hirrK σ' hann' hcomm'

end Representation

namespace Matrix
p2m_export "Matrix" "det_smul trace_sub fromBlocks_add ext fromBlocks_inj row sub_apply traceLinearMap smul_single fromBlocks_smul trace_smul zero map_single det_one diag scalar comp trace_mul_cycle fromBlocks_multiply charpoly trace_mul_comm toLin'_one det_fin_two Nondegenerate toLin'_mul trace_add trace_single_eq_same fromBlocks rank matrix_eq_sum_single det_mul trace_sum zero_apply of_apply single one_apply smul_apply det fromBlocks_zero smul_eq_mulVec add_apply comp_apply of smul_mul trace_zero map toLin' fromBlocks_one one mul_apply trace trace_mul_single module trace_fin_two mulVec SeparatingLeft"
p2m_open "Matrix"

private theorem isSimpleModule_fun_of_field {k : Type*} [Field k] :
    IsSimpleModule (Matrix (Fin 2) (Fin 2) k) (Fin 2 → k) :=
  { eq_bot_or_eq_top := fun U => by
      rcases eq_or_ne U ⊥ with rfl | hU
      · exact Or.inl rfl
      · refine Or.inr (top_unique fun w _ => ?_)

        obtain ⟨v, hvU, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
        obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv0

        have key : (Matrix.of fun i j' => if j' = j then (v j)⁻¹ * w i else 0) • v = w := by
          funext i
          simp only [Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct, Matrix.of_apply]
          rw [Finset.sum_eq_single j]
          · simp only [if_true]; rw [mul_right_comm, inv_mul_cancel₀ hj, one_mul]
          · intro j' _ hne; simp [hne]
          · intro h; exact absurd (Finset.mem_univ j) h
        exact key ▸ U.smul_mem _ hvU }

private theorem isIsotypicOfType_fun_of_field {k : Type*} [Field k]
    {W : Type*} [AddCommGroup W] [Module (Matrix (Fin 2) (Fin 2) k) W] :
    IsIsotypicOfType (Matrix (Fin 2) (Fin 2) k) W (Fin 2 → k) := by
  haveI : IsArtinianRing (Matrix (Fin 2) (Fin 2) k) := IsArtinianRing.of_finite k _
  haveI : IsSimpleModule (Matrix (Fin 2) (Fin 2) k) (Fin 2 → k) := isSimpleModule_fun_of_field
  intro m _

  obtain ⟨Im, ⟨em⟩⟩ :=
    IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule (Matrix (Fin 2) (Fin 2) k) m
  obtain ⟨I0, ⟨e0⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule
    (Matrix (Fin 2) (Fin 2) k) (Fin 2 → k)
  haveI : IsSimpleModule (Matrix (Fin 2) (Fin 2) k) Im := .congr em.symm
  haveI : IsSimpleModule (Matrix (Fin 2) (Fin 2) k) I0 := .congr e0.symm

  have hiso : IsIsotypic (Matrix (Fin 2) (Fin 2) k) (Matrix (Fin 2) (Fin 2) k) :=
    IsSimpleRing.isIsotypic (Matrix (Fin 2) (Fin 2) k) (Matrix (Fin 2) (Fin 2) k)
  obtain ⟨eI⟩ := hiso Im I0
  exact ⟨em.trans (eI.symm.trans e0.symm)⟩

private theorem exists_linearEquiv_fin_fun_of_module
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W]
    [Module (Matrix (Fin 2) (Fin 2) k) W]
    [Module.Finite (Matrix (Fin 2) (Fin 2) k) W] :
    ∃ n : ℕ, Nonempty (W ≃ₗ[Matrix (Fin 2) (Fin 2) k] (Fin n → Fin 2 → k)) :=
  (isIsotypicOfType_fun_of_field (W := W)).linearEquiv_fun

private theorem linearEquiv_matrix_apply_smul
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W]
    [Module (Matrix (Fin 2) (Fin 2) k) W] {n : ℕ}
    (e : W ≃ₗ[Matrix (Fin 2) (Fin 2) k] (Fin n → Fin 2 → k))
    (A : Matrix (Fin 2) (Fin 2) k) (w : W) (i : Fin n) :
    e (A • w) i = A.mulVec (e w i) := by
  rw [e.map_smul, Pi.smul_apply, Matrix.smul_eq_mulVec]

end Matrix

namespace Representation
p2m_export "Representation" "free quotient"
p2m_open "Representation"

variable {k : Type} [Field k] {G : Type} [Group G]
  (ρ : G →* Matrix (Fin 2) (Fin 2) k)
  {W : Type} [AddCommGroup W] [Module k W]

private lemma exists_trace_ne_zero
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤) :
    ∃ x : G, ((ρ x).trace : k) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hle : Submodule.span k (Set.range (fun g : G => ρ g)) ≤
      LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    simpa using hall g
  rw [hirr, top_le_iff, LinearMap.ker_eq_top] at hle
  have h1 : Matrix.traceLinearMap (Fin 2) k k (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : k)) = 1 := by
    simp [Matrix.trace, Matrix.diag, Matrix.single]
  rw [hle] at h1
  simp at h1

variable (σW : Representation k G W)

private lemma sq_eq_trace_smul_sub_det_smul (A : Matrix (Fin 2) (Fin 2) k) :
    A ^ 2 = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.trace_fin_two, Matrix.det_fin_two, smul_eq_mul, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private lemma sq_eq_of_quadratic {R : Type} [Ring R] [Algebra k R] {x : R} {t d : k}
    (hq : x ^ 2 - t • x + d • (1 : R) = 0) :
    x ^ 2 = t • x - d • (1 : R) := by
  have h1 := add_eq_zero_iff_eq_neg.mp hq
  rw [sub_eq_iff_eq_add] at h1
  rw [h1]; abel

private lemma quadratic_inv_formula {R : Type} [Ring R] [Algebra k R]
    {H : Type} [Group H] (f : H →* R) (t d : H → k)
    (hq : ∀ g : H, f g ^ 2 = t g • f g - d g • (1 : R))
    (hd1 : ∀ g : H, d g * d g⁻¹ = 1) (x : H) :
    f x⁻¹ = (d x)⁻¹ • (t x • (1 : R) - f x) := by
  have hd0 : d x ≠ 0 := left_ne_zero_of_mul_eq_one (hd1 x)
  have hq' : f x * (t x • (1 : R) - f x) = d x • 1 := by
    rw [mul_sub, mul_smul_comm, mul_one, ← sq, hq x]; abel
  have hmul : f x⁻¹ * (f x * (t x • (1 : R) - f x)) = f x⁻¹ * (d x • 1) := by rw [hq']
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, mul_smul_comm, mul_one] at hmul
  rw [hmul, smul_smul, inv_mul_cancel₀ hd0, one_smul]

private lemma inv_eq_of_quadratic
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (x : G) :
    σW x⁻¹ = ((ρ x).det)⁻¹ • ((ρ x).trace • (1 : W →ₗ[k] W) - σW x) := by
  have hdet : (ρ x).det * (ρ x⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]
  have hd0 : (ρ x).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet

  have hq : σW x * ((ρ x).trace • (1 : W →ₗ[k] W) - σW x) = (ρ x).det • 1 := by
    have hx2 : (σW x : W →ₗ[k] W) ^ 2 = (ρ x).trace • σW x - (ρ x).det • 1 := by
      have h1 := add_eq_zero_iff_eq_neg.mp (hann x)
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]; abel
    rw [mul_sub, mul_smul_comm, mul_one, ← sq, hx2]
    abel

  have hmul : σW x⁻¹ * (σW x * ((ρ x).trace • (1 : W →ₗ[k] W) - σW x)) =
      σW x⁻¹ * ((ρ x).det • 1) := by rw [hq]
  rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at hmul
  rw [mul_smul_comm, mul_one] at hmul
  rw [hmul, smul_smul, inv_mul_cancel₀ hd0, one_smul]

private lemma sq_sigma (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0) (x : G) :
    (σW x : W →ₗ[k] W) ^ 2 = (ρ x).trace • σW x - (ρ x).det • (1 : W →ₗ[k] W) :=
  sq_eq_of_quadratic (hann x)

private lemma det_mul_det_inv (x : G) : (ρ x).det * (ρ x⁻¹).det = 1 := by
  rw [← Matrix.det_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.det_one]

private lemma trace_smul_bracket
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (g h : G) :
    (ρ g).trace • (σW h * σW g * σW h - (ρ h).det • σW g - (ρ (g * h)).trace • σW h +
      ((ρ g).trace * (ρ h).det) • (1 : W →ₗ[k] W)) = 0 := by
  set a : W →ₗ[k] W := σW g with ha
  set b : W →ₗ[k] W := σW h with hb
  set tg : k := (ρ g).trace with htg
  set th : k := (ρ h).trace with hth
  set tu : k := (ρ (g * h)).trace with htu
  set dg : k := (ρ g).det with hdg
  set dh : k := (ρ h).det with hdh
  have hdg0 : dg ≠ 0 := left_ne_zero_of_mul_eq_one (det_mul_det_inv ρ g)

  have hρq : ∀ x : G, (ρ x) ^ 2 = (ρ x).trace • (ρ x) - (ρ x).det • (1 : Matrix (Fin 2) (Fin 2) k) :=
    fun x => sq_eq_trace_smul_sub_det_smul (ρ x)
  have hρinv := quadratic_inv_formula (k := k) ρ (fun x => (ρ x).trace) (fun x => (ρ x).det)
    hρq (det_mul_det_inv ρ) g

  have hdet_inv : (ρ g⁻¹).det = dg⁻¹ :=
    eq_inv_of_mul_eq_one_right (det_mul_det_inv ρ g)
  have ht' : (ρ (g⁻¹ * h)).trace = dg⁻¹ * (tg * th - tu) := by
    rw [map_mul, hρinv]
    simp only [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.trace_smul,
      Matrix.trace_sub, smul_eq_mul]
    rw [show ρ g * ρ h = ρ (g * h) from (map_mul ρ g h).symm]
  have hd' : (ρ (g⁻¹ * h)).det = dg⁻¹ * dh := by
    rw [map_mul, Matrix.det_mul, hdet_inv]

  have hσinv := quadratic_inv_formula (k := k) (σW : G →* (W →ₗ[k] W))
    (fun x => (ρ x).trace) (fun x => (ρ x).det) (sq_sigma ρ σW hann) (det_mul_det_inv ρ) g
  set Y : W →ₗ[k] W := tg • b - a * b with hY
  have hσgh : (σW (g⁻¹ * h) : W →ₗ[k] W) = dg⁻¹ • Y := by
    rw [map_mul, hσinv, smul_mul_assoc, sub_mul, smul_mul_assoc, one_mul]

  have hkey : Y * Y = (tg * th - tu) • Y - (dg * dh) • (1 : W →ₗ[k] W) := by
    have h0 := sq_sigma ρ σW hann (g⁻¹ * h)
    rw [hσgh, ht', hd', sq] at h0
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul] at h0
    have h1 := congrArg (fun z : W →ₗ[k] W => (dg * dg) • z) h0
    simp only [smul_sub, smul_smul] at h1
    rw [show dg * dg * (dg⁻¹ * dg⁻¹) = 1 from by field_simp, one_smul] at h1
    rw [show dg * dg * (dg⁻¹ * (tg * th - tu) * dg⁻¹) = tg * th - tu from by field_simp] at h1
    rw [show dg * dg * (dg⁻¹ * dh) = dg * dh from by field_simp] at h1
    exact h1

  have hb2 : b * b = th • b - dh • (1 : W →ₗ[k] W) := by
    have := sq_sigma ρ σW hann h; rwa [sq, ← hb, ← hth, ← hdh] at this
  have hab2 : a * (b * (a * b)) = tu • (a * b) - (dg * dh) • (1 : W →ₗ[k] W) := by
    have h0 := sq_sigma ρ σW hann (g * h)
    rw [map_mul σW, ← ha, ← hb, sq, mul_assoc] at h0
    rw [h0, ← htu]
    congr 2
    rw [show ρ (g * h) = ρ g * ρ h from map_mul ρ g h, Matrix.det_mul, ← hdg, ← hdh]

  have hYY : Y * Y = (tg * tg) • (b * b) - tg • (b * (a * b)) - tg • (a * (b * b)) +
      a * (b * (a * b)) := by
    rw [hY]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_assoc]
    match_scalars <;> ring

  have hmain : tg • (b * (a * b)) - (tg * dh) • a - (tg * tu) • b +
      (tg * (tg * dh)) • (1 : W →ₗ[k] W) = 0 := by
    have h2 := hkey
    rw [hYY, hY, hb2, hab2] at h2
    rw [mul_sub a (th • b) (dh • (1 : W →ₗ[k] W)), mul_smul_comm, mul_smul_comm, mul_one] at h2
    have h3 := sub_eq_zero.mpr h2
    rw [← neg_eq_zero, ← h3]
    match_scalars <;> ring

  have hgoal : tg • (b * a * b - dh • a - tu • b + (tg * dh) • (1 : W →ₗ[k] W)) =
      tg • (b * (a * b)) - (tg * dh) • a - (tg * tu) • b +
      (tg * (tg * dh)) • (1 : W →ₗ[k] W) := by
    rw [mul_assoc]
    match_scalars <;> ring
  rw [hgoal, hmain]

private def polZ (g h : G) : W →ₗ[k] W :=
  σW g * σW h + σW h * σW g - (ρ g).trace • σW h - (ρ h).trace • σW g +
    ((ρ g).trace * (ρ h).trace - (ρ (g * h)).trace) • (1 : W →ₗ[k] W)

private lemma polZ_symm (g h : G) : polZ ρ σW g h = polZ ρ σW h g := by
  unfold polZ
  have htr : (ρ (g * h)).trace = (ρ (h * g)).trace := by
    rw [map_mul, map_mul, Matrix.trace_mul_comm]
  rw [htr]
  match_scalars <;> ring

private lemma trace_smul_polZ
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (g h : G) :
    (ρ g).trace • polZ ρ σW g h = 0 := by
  set a : W →ₗ[k] W := σW g with ha
  set b : W →ₗ[k] W := σW h with hb
  set tg : k := (ρ g).trace with htg
  set th : k := (ρ h).trace with hth
  set tu : k := (ρ (g * h)).trace with htu
  set dg : k := (ρ g).det with hdg
  set dh : k := (ρ h).det with hdh
  have hdh0 : dh ≠ 0 := left_ne_zero_of_mul_eq_one (det_mul_det_inv ρ h)
  have hσinvh : (σW h⁻¹ : W →ₗ[k] W) = dh⁻¹ • (th • (1 : W →ₗ[k] W) - b) := by
    rw [quadratic_inv_formula (k := k) (σW : G →* (W →ₗ[k] W))
      (fun x => (ρ x).trace) (fun x => (ρ x).det) (sq_sigma ρ σW hann) (det_mul_det_inv ρ) h,
      ← hdh, ← hth, ← hb]
  have hb2 : b * b = th • b - dh • (1 : W →ₗ[k] W) := by
    have := sq_sigma ρ σW hann h; rwa [sq, ← hb, ← hth, ← hdh] at this
  have hbinv : b * σW h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hB := trace_smul_bracket ρ σW hann g h
  have hB' := congrArg (fun z : W →ₗ[k] W => z * σW h⁻¹) hB
  simp only [smul_mul_assoc, zero_mul] at hB'

  have hred : (b * a * b - dh • a - tu • b + (tg * dh) • (1 : W →ₗ[k] W)) * σW h⁻¹ =
      dh⁻¹ • (dh • polZ ρ σW g h) := by
    rw [hσinvh]
    simp only [mul_smul_comm, add_mul, sub_mul, smul_mul_assoc, mul_sub, mul_one, mul_assoc]
    rw [hb2]
    simp only [mul_sub, mul_smul_comm, mul_one]
    unfold polZ
    rw [← ha, ← hb, ← htg, ← hth, ← htu]
    match_scalars <;> field_simp <;> ring
  rw [hred, smul_smul, smul_smul] at hB'
  rw [show tg * dh⁻¹ * dh = (ρ g).trace from by
    rw [mul_assoc, inv_mul_cancel₀ hdh0, mul_one, htg]] at hB'
  exact hB'

private lemma trace_smul_polZ' (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (g h : G) :
    (ρ h).trace • polZ ρ σW g h = 0 := by
  rw [polZ_symm]
  exact trace_smul_polZ ρ σW hann h g

private lemma trace_mul_smul_polZ
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (g h : G) :
    (ρ (g * h)).trace • polZ ρ σW g h = 0 := by
  set a : W →ₗ[k] W := σW g with ha
  set b : W →ₗ[k] W := σW h with hb
  set tg : k := (ρ g).trace with htg
  set th : k := (ρ h).trace with hth
  set tu : k := (ρ (g * h)).trace with htu
  set dg : k := (ρ g).det with hdg
  set dh : k := (ρ h).det with hdh
  have hdh0 : dh ≠ 0 := left_ne_zero_of_mul_eq_one (det_mul_det_inv ρ h)
  have hdet_invh : (ρ h⁻¹).det = dh⁻¹ :=
    eq_inv_of_mul_eq_one_right (det_mul_det_inv ρ h)
  have hσinvh : (σW h⁻¹ : W →ₗ[k] W) = dh⁻¹ • (th • (1 : W →ₗ[k] W) - b) := by
    rw [quadratic_inv_formula (k := k) (σW : G →* (W →ₗ[k] W))
      (fun x => (ρ x).trace) (fun x => (ρ x).det) (sq_sigma ρ σW hann) (det_mul_det_inv ρ) h,
      ← hdh, ← hth, ← hb]
  have hb2 : b * b = th • b - dh • (1 : W →ₗ[k] W) := by
    have := sq_sigma ρ σW hann h; rwa [sq, ← hb, ← hth, ← hdh] at this
  have hB := trace_smul_bracket ρ σW hann (g * h) h⁻¹
  rw [show g * h * h⁻¹ = g from by group] at hB
  rw [map_mul σW, ← ha, ← hb, hdet_invh, hσinvh, ← htu, ← htg] at hB
  have hred : dh⁻¹ • (th • (1 : W →ₗ[k] W) - b) * (a * b) * (dh⁻¹ • (th • (1 : W →ₗ[k] W) - b)) -
      dh⁻¹ • (a * b) - tg • (dh⁻¹ • (th • (1 : W →ₗ[k] W) - b)) +
      (tu * dh⁻¹) • (1 : W →ₗ[k] W) = -(dh⁻¹ • polZ ρ σW g h) := by
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, one_mul, mul_one,
      mul_assoc]
    rw [hb2]
    simp only [mul_sub, mul_smul_comm, mul_one]
    unfold polZ
    rw [← ha, ← hb, ← htg, ← hth, ← htu]
    match_scalars <;> field_simp <;> ring
  rw [hred] at hB
  rw [smul_neg, neg_eq_zero, smul_smul] at hB
  have hB2 := congrArg (fun z : W →ₗ[k] W => dh • z) hB
  simp only [smul_smul, smul_zero] at hB2
  rw [show dh * (tu * dh⁻¹) = tu from by field_simp] at hB2
  exact hB2

private lemma polZ_eq_zero
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (g h : G) :
    polZ ρ σW g h = 0 := by
  by_cases hg : (ρ g).trace = 0
  · by_cases hh : (ρ h).trace = 0
    · by_cases hgh : (ρ (g * h)).trace = 0
      ·
        set a : W →ₗ[k] W := σW g with ha
        set b : W →ₗ[k] W := σW h with hb
        set dg : k := (ρ g).det with hdg
        set dh : k := (ρ h).det with hdh
        have hdg0 : dg ≠ 0 := left_ne_zero_of_mul_eq_one (det_mul_det_inv ρ g)
        have hdh0 : dh ≠ 0 := left_ne_zero_of_mul_eq_one (det_mul_det_inv ρ h)
        have ha2 : a * a = -(dg • (1 : W →ₗ[k] W)) := by
          have h0 := hann g
          rw [hg, zero_smul, sub_zero, sq, ← ha, ← hdg] at h0
          exact eq_neg_of_add_eq_zero_left h0
        have hb2 : b * b = -(dh • (1 : W →ₗ[k] W)) := by
          have h0 := hann h
          rw [hh, zero_smul, sub_zero, sq, ← hb, ← hdh] at h0
          exact eq_neg_of_add_eq_zero_left h0
        have hab2 : (a * b) * (a * b) = -((dg * dh) • (1 : W →ₗ[k] W)) := by
          have h0 := hann (g * h)
          rw [hgh, zero_smul, sub_zero, sq, map_mul σW, ← ha, ← hb] at h0
          rw [show (ρ (g * h)).det = dg * dh from by
            rw [map_mul, Matrix.det_mul, ← hdg, ← hdh]] at h0
          exact eq_neg_of_add_eq_zero_left h0
        have h1 : a * ((a * b) * (a * b)) * b = (dg * dh) • (b * a) := by
          rw [show a * ((a * b) * (a * b)) * b = (a * a) * ((b * a) * (b * b)) from by
            noncomm_ring]
          rw [ha2, hb2]
          simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
          match_scalars; ring
        have h2 : a * ((a * b) * (a * b)) * b = -((dg * dh) • (a * b)) := by
          rw [hab2]
          simp only [mul_neg, neg_mul, smul_mul_assoc, mul_smul_comm, mul_one]
        have hba : b * a = -(a * b) := by
          have h3 : (dg * dh) • (b * a) = -((dg * dh) • (a * b)) := by rw [← h1, h2]
          have h4 := congrArg (fun z : W →ₗ[k] W => (dg * dh)⁻¹ • z) h3
          simp only [smul_smul, smul_neg] at h4
          rw [inv_mul_cancel₀ (mul_ne_zero hdg0 hdh0)] at h4
          simp only [one_smul] at h4
          exact h4
        unfold polZ
        rw [hg, hh, hgh, ← ha, ← hb, hba]
        simp
      · have hZ := trace_mul_smul_polZ ρ σW hann g h
        exact (smul_eq_zero.mp hZ).resolve_left hgh
    · have hZ := trace_smul_polZ' ρ σW hann g h
      exact (smul_eq_zero.mp hZ).resolve_left hh
  · have hZ := trace_smul_polZ ρ σW hann g h
    exact (smul_eq_zero.mp hZ).resolve_left hg

private lemma sigma_mul_relation_add_relation_mul_sigma
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (c : G →₀ k) (hc : (c.sum fun g a => a • ρ g) = 0) (h : G) :
    σW h * (c.sum fun g a => a • (σW g : W →ₗ[k] W)) +
      (c.sum fun g a => a • (σW g : W →ₗ[k] W)) * σW h =
      (ρ h).trace • (c.sum fun g a => a • (σW g : W →ₗ[k] W)) := by
  classical

  have htr1 : (∑ g ∈ c.support, c g * (ρ g).trace) = 0 := by
    have := congrArg Matrix.trace hc
    rw [Finsupp.sum] at this
    simpa [Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul] using this
  have htr2 : (∑ g ∈ c.support, c g * (ρ (g * h)).trace) = 0 := by
    have h0 := congrArg (fun X : Matrix (Fin 2) (Fin 2) k => Matrix.trace (X * ρ h)) hc
    rw [Finsupp.sum] at h0
    simp only [Finset.sum_mul, Matrix.smul_mul, Matrix.zero_mul, Matrix.trace_zero,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul] at h0
    have hrw : ∀ g : G, (ρ g * ρ h).trace = (ρ (g * h)).trace := fun g => by rw [← map_mul]
    simpa [hrw] using h0

  simp only [Finsupp.sum]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]

  have hterm : ∀ g' : G, (σW h : W →ₗ[k] W) * σW g' + σW g' * σW h =
      (ρ g').trace • σW h + (ρ h).trace • σW g' -
        ((ρ g').trace * (ρ h).trace - (ρ (g' * h)).trace) • (1 : W →ₗ[k] W) := by
    intro g'
    have hZ := polZ_eq_zero ρ σW hann g' h
    rw [← sub_eq_zero, ← hZ]
    unfold polZ
    match_scalars <;> ring
  calc (∑ g' ∈ c.support, (σW h * (c g' • σW g') + (c g' • σW g') * σW h))
      = ∑ g' ∈ c.support, ((c g' * (ρ g').trace) • (σW h : W →ₗ[k] W) +
          (ρ h).trace • (c g' • σW g') -
          (c g' * ((ρ g').trace * (ρ h).trace - (ρ (g' * h)).trace)) • (1 : W →ₗ[k] W)) := by
        apply Finset.sum_congr rfl
        intro g' _
        rw [mul_smul_comm, smul_mul_assoc, ← smul_add, hterm g']
        match_scalars <;> ring
    _ = (∑ g' ∈ c.support, c g' * (ρ g').trace) • (σW h : W →ₗ[k] W) +
          (ρ h).trace • (∑ g' ∈ c.support, c g' • (σW g' : W →ₗ[k] W)) -
          ((∑ g' ∈ c.support, c g' * (ρ g').trace) * (ρ h).trace -
            (∑ g' ∈ c.support, c g' * (ρ (g' * h)).trace)) • (1 : W →ₗ[k] W) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, Finset.smul_sum,
          ← Finset.sum_smul]
        congr 2
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro g' _
        ring
    _ = (ρ h).trace • ∑ g' ∈ c.support, c g' • (σW g' : W →ₗ[k] W) := by
        rw [htr1, htr2]
        simp

private lemma mul_sigma_mul_sub_of_anticomm
    (U : W →ₗ[k] W)
    (hU : ∀ h : G, σW h * U + U * σW h = (ρ h).trace • U)
    (x y : G) :
    U * (σW x * σW y) - σW x * σW y * U =
      ((ρ x).trace * (ρ y).trace) • U - (ρ x).trace • (σW y * U) -
        (ρ y).trace • ((σW x : W →ₗ[k] W) * U) := by
  have e1 : (U : W →ₗ[k] W) * σW x = (ρ x).trace • U - σW x * U := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hU x
  have e2 : (U : W →ₗ[k] W) * σW y = (ρ y).trace • U - σW y * U := by
    rw [eq_sub_iff_add_eq, add_comm]; exact hU y
  calc U * (σW x * σW y) - σW x * σW y * U
      = (U * σW x) * σW y - σW x * (σW y * U) := by rw [mul_assoc, mul_assoc]
    _ = ((ρ x).trace • U - σW x * U) * σW y - σW x * (σW y * U) := by rw [e1]
    _ = (ρ x).trace • (U * σW y) - σW x * (U * σW y) - σW x * (σW y * U) := by
        rw [sub_mul, smul_mul_assoc, mul_assoc]
    _ = (ρ x).trace • ((ρ y).trace • U - σW y * U) -
          σW x * ((ρ y).trace • U - σW y * U) - σW x * (σW y * U) := by rw [e2]
    _ = ((ρ x).trace * (ρ y).trace) • U - (ρ x).trace • (σW y * U) -
          (ρ y).trace • ((σW x : W →ₗ[k] W) * U) := by
        rw [mul_sub, mul_smul_comm]
        match_scalars <;> ring

private lemma commutator_mul_eq_zero_of_anticomm
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (U : W →ₗ[k] W)
    (hU : ∀ h : G, σW h * U + U * σW h = (ρ h).trace • U)
    (h h' : G) :
    (σW h * σW h' - σW h' * σW h) * U = 0 := by
  set th : k := (ρ h).trace with hth
  set th' : k := (ρ h').trace with hth'
  set tu : k := (ρ (h * h')).trace with htu

  have hA : U * (σW h * σW h') - σW h * σW h' * U =
      (th * th') • U - th • (σW h' * U) - th' • ((σW h : W →ₗ[k] W) * U) := by
    have e1 : (U : W →ₗ[k] W) * σW h = th • U - σW h * U := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hU h
    have e2 : (U : W →ₗ[k] W) * σW h' = th' • U - σW h' * U := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hU h'
    calc U * (σW h * σW h') - σW h * σW h' * U
        = (U * σW h) * σW h' - σW h * (σW h' * U) := by rw [mul_assoc, mul_assoc]
      _ = (th • U - σW h * U) * σW h' - σW h * (σW h' * U) := by rw [e1]
      _ = th • (U * σW h') - σW h * (U * σW h') - σW h * (σW h' * U) := by
          rw [sub_mul, smul_mul_assoc, mul_assoc]
      _ = th • (th' • U - σW h' * U) - σW h * (th' • U - σW h' * U) - σW h * (σW h' * U) := by
          rw [e2]
      _ = (th * th') • U - th • (σW h' * U) - th' • ((σW h : W →ₗ[k] W) * U) := by
          rw [mul_sub, mul_smul_comm]
          match_scalars <;> ring

  have hC : σW h * σW h' * U + U * (σW h * σW h') = tu • U := by
    have := hU (h * h')
    rwa [map_mul σW] at this

  have hD : (σW h * σW h' + σW h' * σW h) * U =
      th • (σW h' * U) + th' • ((σW h : W →ₗ[k] W) * U) - (th * th' - tu) • U := by
    have hZ := polZ_eq_zero ρ σW hann h h'
    unfold polZ at hZ
    have h0 := congrArg (fun z : W →ₗ[k] W => z * U) hZ
    simp only [zero_mul] at h0
    rw [← sub_eq_zero]
    rw [← h0]
    simp only [add_mul, sub_mul, smul_mul_assoc, one_mul]
    rw [← hth, ← hth', ← htu]
    match_scalars <;> ring

  have hE : σW h * σW h' * U + σW h * σW h' * U =
      tu • U - (th * th') • U + th • (σW h' * U) + th' • ((σW h : W →ₗ[k] W) * U) := by
    have := hC
    rw [show U * (σW h * σW h') =
      σW h * σW h' * U + ((th * th') • U - th • (σW h' * U) - th' • ((σW h : W →ₗ[k] W) * U))
      from by rw [← hA]; abel] at this
    rw [← sub_eq_zero] at this ⊢
    rw [← this]
    abel
  rw [sub_mul, sub_eq_zero]
  have := hE
  rw [show tu • U - (th * th') • U + th • (σW h' * U) + th' • ((σW h : W →ₗ[k] W) * U) =
    (σW h * σW h' + σW h' * σW h) * U from by rw [hD]; match_scalars <;> ring] at this
  rw [add_mul] at this

  exact add_left_cancel this

private lemma mul_commutator_eq_zero_of_anticomm
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (U : W →ₗ[k] W)
    (hU : ∀ h : G, σW h * U + U * σW h = (ρ h).trace • U)
    (h h' : G) :
    U * (σW h * σW h' - σW h' * σW h) = 0 := by
  have k1 := mul_sigma_mul_sub_of_anticomm ρ σW U hU h h'
  have k2 := mul_sigma_mul_sub_of_anticomm ρ σW U hU h' h
  have hint : U * (σW h * σW h' - σW h' * σW h) =
      (σW h * σW h' - σW h' * σW h) * U := by
    rw [mul_sub, sub_mul, ← sub_eq_zero]
    have h12 : (U * (σW h * σW h') - σW h * σW h' * U) -
        (U * (σW h' * σW h) - σW h' * σW h * U) = 0 := by
      rw [k1, k2, ← sub_eq_zero]
      match_scalars <;> ring
    rw [← h12]
    abel
  rw [hint]
  exact commutator_mul_eq_zero_of_anticomm ρ σW hann U hU h h'

private lemma relations_lift [FiniteDimensional k W]
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0)
    (c : G →₀ k) (hc : (c.sum fun g a => a • ρ g) = 0) :
    (c.sum fun g a => a • (σW g : W →ₗ[k] W)) = 0 := by
  rcases subsingleton_or_nontrivial W with hW | hW
  · exact Subsingleton.elim _ _
  set U : W →ₗ[k] W := c.sum fun g a => a • (σW g : W →ₗ[k] W) with hUdef
  have hU : ∀ h : G, σW h * U + U * σW h = (ρ h).trace • U := fun h =>
    sigma_mul_relation_add_relation_mul_sigma ρ σW hann c hc h

  set C : Submodule k W :=
    ⨆ p : G × G, LinearMap.range (σW p.1 * σW p.2 - σW p.2 * σW p.1 : W →ₗ[k] W) with hCdef
  have hgen : ∀ (h h' : G) (z : W), (σW h * σW h' - σW h' * σW h : W →ₗ[k] W) z ∈ C := by
    intro h h' z
    exact Submodule.mem_iSup_of_mem (h, h') (LinearMap.mem_range_self _ z)

  have hconj : ∀ g h h' : G, (σW g : W →ₗ[k] W) * (σW h * σW h' - σW h' * σW h) =
      (σW (g * h * g⁻¹) * σW (g * h' * g⁻¹) - σW (g * h' * g⁻¹) * σW (g * h * g⁻¹) :
        W →ₗ[k] W) * σW g := by
    intro g h h'
    have e1 : (σW g : W →ₗ[k] W) * (σW h * σW h') =
        (σW (g * h * g⁻¹) * σW (g * h' * g⁻¹) : W →ₗ[k] W) * σW g := by
      rw [← map_mul σW, ← map_mul σW, ← map_mul σW, ← map_mul σW]
      exact congrArg σW (by group)
    have e2 : (σW g : W →ₗ[k] W) * (σW h' * σW h) =
        (σW (g * h' * g⁻¹) * σW (g * h * g⁻¹) : W →ₗ[k] W) * σW g := by
      rw [← map_mul σW, ← map_mul σW, ← map_mul σW, ← map_mul σW]
      exact congrArg σW (by group)
    rw [mul_sub, sub_mul, e1, e2]
  have hstab : ∀ (g : G), ∀ x ∈ C, σW g x ∈ C := by
    intro g x hx
    refine Submodule.iSup_induction
      (p := fun q : G × G =>
        LinearMap.range (σW q.1 * σW q.2 - σW q.2 * σW q.1 : W →ₗ[k] W))
      (motive := fun y => σW g y ∈ C) hx ?_ ?_ ?_
    · rintro ⟨h, h'⟩ y ⟨z, rfl⟩
      have := LinearMap.congr_fun (hconj g h h') z
      simp only [Module.End.mul_apply] at this
      rw [this]
      exact hgen _ _ _
    · simp only [map_zero]
      exact Submodule.zero_mem C
    · intro y₁ y₂ m₁ m₂
      rw [map_add]
      exact Submodule.add_mem C m₁ m₂

  have hCtop : C = ⊤ := by
    by_contra hne
    haveI : Nontrivial (W ⧸ C) := Submodule.Quotient.nontrivial_iff.mpr hne
    have hle : ∀ g : G, C ≤ C.comap (σW g) := fun g x hx => hstab g x hx
    let σq : G → ((W ⧸ C) →ₗ[k] (W ⧸ C)) := fun g => C.mapQ C (σW g) (hle g)
    have hσq_apply : ∀ (g : G) (y : W),
        σq g (Submodule.Quotient.mk y) = Submodule.Quotient.mk (σW g y) := fun g y => rfl
    have hσq_mul : ∀ g h : G, σq (g * h) = σq g * σq h := by
      intro g h
      refine Submodule.linearMap_qext _ ?_
      ext x
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply, hσq_apply,
        map_mul σW]
    let σWq : Representation k G (W ⧸ C) :=
      { toFun := σq
        map_one' := by
          refine Submodule.linearMap_qext _ ?_
          ext x
          simp only [LinearMap.comp_apply, Submodule.mkQ_apply, hσq_apply, map_one σW,
            Module.End.one_apply]
        map_mul' := hσq_mul }
    have hσWq_apply : ∀ (g : G) (y : W),
        σWq g (Submodule.Quotient.mk y) = Submodule.Quotient.mk (σW g y) := fun g y => rfl
    have hannq : ∀ g : G,
        σWq g ^ 2 - Matrix.trace (ρ g) • σWq g + (ρ g).det • (1 : (W ⧸ C) →ₗ[k] (W ⧸ C)) = 0 := by
      intro g
      refine Submodule.linearMap_qext _ ?_
      ext x
      have h0 := LinearMap.congr_fun (hann g) x
      simp only [pow_two, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.mul_apply, Module.End.one_apply, LinearMap.zero_apply] at h0
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.zero_apply, pow_two,
        LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
        Module.End.one_apply, hσWq_apply, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub,
        ← Submodule.Quotient.mk_add]
      rw [Submodule.Quotient.mk_eq_zero, h0]
      exact Submodule.zero_mem C
    have hcommq : ∀ g h : G, Commute (σWq g : (W ⧸ C) →ₗ[k] (W ⧸ C)) (σWq h) := by
      intro g h
      unfold Commute SemiconjBy
      refine Submodule.linearMap_qext _ ?_
      ext x
      simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply, hσWq_apply]
      rw [Submodule.Quotient.eq]
      have he : σW g (σW h x) - σW h (σW g x) =
          (σW g * σW h - σW h * σW g : W →ₗ[k] W) x := by
        simp [Module.End.mul_apply]
      rw [he]
      exact hgen g h x
    exact (commuting_hann_spanTop_isFalse ρ hirr σWq hannq hcommq).elim

  have hCker : C ≤ LinearMap.ker U := by
    refine iSup_le fun q => LinearMap.range_le_ker_iff.mpr ?_
    rw [← Module.End.mul_eq_comp]
    exact mul_commutator_eq_zero_of_anticomm ρ σW hann U hU q.1 q.2
  have hker_top : LinearMap.ker U = ⊤ := top_unique (hCtop ▸ hCker)
  exact LinearMap.ker_eq_top.mp hker_top

section E1

private lemma polCH_fin_two (A D : Matrix (Fin 2) (Fin 2) k) :
    A * D + D * A - A.trace • D - D.trace • A +
      (A.trace * D.trace - (A * D).trace) • (1 : Matrix (Fin 2) (Fin 2) k) = 0 := by
  ext i j
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private def blockMat (δ : G → Matrix (Fin 2) (Fin 2) k) (g : G) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k :=
  Matrix.fromBlocks (ρ g) (δ g) 0 (ρ g)

private lemma fromBlocks_sub' (A B C D A' B' C' D' : Matrix (Fin 2) (Fin 2) k) :
    Matrix.fromBlocks A B C D - Matrix.fromBlocks A' B' C' D' =
      Matrix.fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext (i | i) (j | j) <;> rfl

private lemma fromBlocks_finset_sum {ι : Type} (s : Finset ι) (A B C D : ι → Matrix (Fin 2) (Fin 2) k) :
    ∑ i ∈ s, Matrix.fromBlocks (A i) (B i) (C i) (D i) =
      Matrix.fromBlocks (∑ i ∈ s, A i) (∑ i ∈ s, B i) (∑ i ∈ s, C i) (∑ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.fromBlocks_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, ih, Matrix.fromBlocks_add, Finset.sum_insert ha,
      Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]

private theorem exists_eq_conj_sub_of_cocycle_of_trace_eq_zero
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (δ : G → Matrix (Fin 2) (Fin 2) k)
    (hδ : ∀ g h, δ (g * h) = ρ g * δ h + δ g * ρ h)
    (htr : ∀ g, (δ g).trace = 0) (htrρ : ∀ g, (ρ g * δ g).trace = 0) :
    ∃ M : Matrix (Fin 2) (Fin 2) k, ∀ g, δ g = ρ g * M - M * ρ g := by
  classical

  have hblock : ∀ g, ρ g * δ g + δ g * ρ g = (ρ g).trace • δ g := by
    intro g
    have h := polCH_fin_two (ρ g) (δ g)
    rw [htr, htrρ, zero_smul, sub_zero, mul_zero, sub_zero, zero_smul, add_zero] at h
    exact sub_eq_zero.mp h
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    rw [mul_one, map_one, one_mul, mul_one] at h
    have h' : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have hCH : ∀ g, ρ g * ρ g = (ρ g).trace • ρ g - (ρ g).det • (1 : Matrix (Fin 2) (Fin 2) k) := by
    intro g; rw [← sq]; exact sq_eq_trace_smul_sub_det_smul (ρ g)

  have hBmul : ∀ g h, blockMat ρ δ (g * h) = blockMat ρ δ g * blockMat ρ δ h := by
    intro g h
    simp only [blockMat, Matrix.fromBlocks_multiply, map_mul, hδ, Matrix.mul_zero, Matrix.zero_mul, add_zero,
      zero_add]
  have hB1 : blockMat ρ δ 1 = 1 := by
    simp only [blockMat, map_one, hδ1, Matrix.fromBlocks_one]
  have hBann : ∀ g, blockMat ρ δ g * blockMat ρ δ g - (ρ g).trace • blockMat ρ δ g +
      (ρ g).det • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) = 0 := by
    intro g
    have key : blockMat ρ δ g * blockMat ρ δ g =
        (ρ g).trace • blockMat ρ δ g - (ρ g).det • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) := by
      rw [← Matrix.fromBlocks_one]
      simp only [blockMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, fromBlocks_sub',
        Matrix.fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [Matrix.mul_zero, add_zero]; exact hCH g
      · rw [smul_zero, sub_zero]; exact hblock g
      · simp
      · rw [Matrix.zero_mul, zero_add]; exact hCH g
    rw [key]; abel
  let σ : Representation k G ((Fin 2 ⊕ Fin 2) → k) :=
    { toFun := fun g => Matrix.toLin' (blockMat ρ δ g)
      map_one' := by simp only [hB1, Matrix.toLin'_one]; rfl
      map_mul' := fun g h => by simp only [hBmul, Matrix.toLin'_mul]; rfl }
  have hσ : ∀ g, (σ g : ((Fin 2 ⊕ Fin 2) → k) →ₗ[k] ((Fin 2 ⊕ Fin 2) → k)) = Matrix.toLin' (blockMat ρ δ g) :=
    fun g => rfl
  have hannσ : ∀ g : G, σ g ^ 2 - Matrix.trace (ρ g) • σ g +
      (ρ g).det • (1 : ((Fin 2 ⊕ Fin 2) → k) →ₗ[k] ((Fin 2 ⊕ Fin 2) → k)) = 0 := by
    intro g
    have : σ g ^ 2 - Matrix.trace (ρ g) • σ g + (ρ g).det • (1 : ((Fin 2 ⊕ Fin 2) → k) →ₗ[k] _) =
        Matrix.toLin' (blockMat ρ δ g * blockMat ρ δ g - (ρ g).trace • blockMat ρ δ g +
          (ρ g).det • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)) := by
      rw [map_add, map_sub, map_smul, map_smul, Matrix.toLin'_mul, Matrix.toLin'_one, sq, hσ]; rfl
    rw [this, hBann, map_zero]

  have hY : ∀ c : G →₀ k, (c.sum fun g a => a • ρ g) = 0 → (c.sum fun g a => a • δ g) = 0 := by
    intro c hc
    set Y : Matrix (Fin 2) (Fin 2) k := c.sum fun g a => a • δ g with hYdef

    have hU : (c.sum fun g a => a • blockMat ρ δ g) = Matrix.fromBlocks 0 Y 0 0 := by
      have hc' : ∑ g ∈ c.support, c g • ρ g = 0 := by simpa only [Finsupp.sum] using hc
      simp only [Finsupp.sum, blockMat, Matrix.fromBlocks_smul, smul_zero, fromBlocks_finset_sum,
        Finset.sum_const_zero, hc']
      rw [hYdef, Finsupp.sum]
    have hXρ : ∀ h : G, ρ h * Y + Y * ρ h = (ρ h).trace • Y := by
      intro h
      have hstar := sigma_mul_relation_add_relation_mul_sigma ρ σ hannσ c hc h
      have hsumσ : (c.sum fun g a => a • (σ g : ((Fin 2 ⊕ Fin 2) → k) →ₗ[k] ((Fin 2 ⊕ Fin 2) → k))) =
          Matrix.toLin' (c.sum fun g a => a • blockMat ρ δ g) := by
        simp only [Finsupp.sum, map_sum, map_smul, hσ]
      rw [hsumσ, hσ, Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
        ← Matrix.toLin'_mul, ← map_add, ← map_smul, hU] at hstar
      have hmat := Matrix.toLin'.injective hstar
      simp only [blockMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, Matrix.fromBlocks_smul,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_zero] at hmat
      exact (Matrix.fromBlocks_inj.mp hmat).2.1

    have hXall : ∀ X : Matrix (Fin 2) (Fin 2) k, X * Y + Y * X = X.trace • Y := by
      intro X
      have hX : X ∈ Submodule.span k (Set.range (fun g : G => ρ g)) := by rw [hirr]; exact Submodule.mem_top
      refine Submodule.span_induction (p := fun X _ => X * Y + Y * X = X.trace • Y) ?_ ?_ ?_ ?_ hX
      · rintro _ ⟨h, rfl⟩; exact hXρ h
      · simp
      · intro x y _ _ hx hy
        rw [add_mul, mul_add, Matrix.trace_add, add_smul, ← hx, ← hy]; abel
      · intro a x _ hx
        rw [smul_mul_assoc, mul_smul_comm, ← smul_add, hx, Matrix.trace_smul, smul_assoc]

    have ent : ∀ (X : Matrix (Fin 2) (Fin 2) k) (i j : Fin 2), (X * Y + Y * X) i j = X.trace * Y i j := by
      intro X i j
      have := congrFun (congrFun (hXall X) i) j
      simpa only [Matrix.smul_apply, smul_eq_mul] using this
    have y00 : Y 0 0 = 0 := by
      have e := ent (Matrix.single 0 0 1) 0 0
      simp [Matrix.mul_apply, Matrix.single, Matrix.trace_fin_two] at e
      linear_combination e
    have y11 : Y 1 1 = 0 := by
      have e := ent (Matrix.single 0 0 1) 1 1
      simp [Matrix.mul_apply, Matrix.single, Matrix.trace_fin_two] at e
      linear_combination -e
    have y10 : Y 1 0 = 0 := by
      have e := ent (Matrix.single 0 1 1) 0 0
      simp [Matrix.mul_apply, Matrix.single, Matrix.trace_fin_two] at e
      linear_combination e
    have y01 : Y 0 1 = 0 := by
      have e := ent (Matrix.single 1 0 1) 1 1
      simp [Matrix.mul_apply, Matrix.single, Matrix.trace_fin_two] at e
      linear_combination e
    ext i j
    fin_cases i <;> fin_cases j <;> simp [y00, y01, y10, y11]

  let L : (G →₀ k) →ₗ[k] Matrix (Fin 2) (Fin 2) k := Finsupp.linearCombination k (fun g => ρ g)
  let Δ : (G →₀ k) →ₗ[k] Matrix (Fin 2) (Fin 2) k := Finsupp.linearCombination k δ
  have hLsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    show LinearMap.range (Finsupp.linearCombination k (fun g => ρ g)) = ⊤
    rw [Finsupp.range_linearCombination, hirr]
  have hker : LinearMap.ker L ≤ LinearMap.ker Δ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    show Finsupp.linearCombination k δ c = 0
    rw [Finsupp.linearCombination_apply]
    apply hY
    rw [← Finsupp.linearCombination_apply]
    exact hc
  let D : Matrix (Fin 2) (Fin 2) k →ₗ[k] Matrix (Fin 2) (Fin 2) k :=
    (LinearMap.ker L).liftQ Δ hker ∘ₗ (L.quotKerEquivOfSurjective hLsurj).symm.toLinearMap
  have hDL : ∀ c, D (L c) = Δ c := by
    intro c
    show (LinearMap.ker L).liftQ Δ hker ((L.quotKerEquivOfSurjective hLsurj).symm (L c)) = Δ c
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hDρ : ∀ g, D (ρ g) = δ g := by
    intro g
    have h1 : L (Finsupp.single g 1) = ρ g := by
      show Finsupp.linearCombination k (fun g => ρ g) (Finsupp.single g 1) = ρ g
      rw [Finsupp.linearCombination_single, one_smul]
    have h2 : Δ (Finsupp.single g 1) = δ g := by
      show Finsupp.linearCombination k δ (Finsupp.single g 1) = δ g
      rw [Finsupp.linearCombination_single, one_smul]
    rw [← h1, hDL, h2]

  have hder : ∀ X Z : Matrix (Fin 2) (Fin 2) k, D (X * Z) = X * D Z + D X * Z := by
    intro X Z
    have hX : X ∈ Submodule.span k (Set.range (fun g : G => ρ g)) := by rw [hirr]; exact Submodule.mem_top
    have hZ : Z ∈ Submodule.span k (Set.range (fun g : G => ρ g)) := by rw [hirr]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun Z _ => D (X * Z) = X * D Z + D X * Z) ?_ ?_ ?_ ?_ hZ
    · rintro _ ⟨h, rfl⟩
      refine Submodule.span_induction (p := fun X _ => D (X * ρ h) = X * D (ρ h) + D X * ρ h) ?_ ?_ ?_ ?_ hX
      · rintro _ ⟨g, rfl⟩
        rw [← map_mul, hDρ, hDρ, hDρ, hδ]
      · simp
      · intro x y _ _ hx hy
        simp only [add_mul, map_add, hx, hy]; abel
      · intro a x _ hx
        simp only [smul_mul_assoc, map_smul, hx, smul_add]
    · simp
    · intro x y _ _ hx hy
      simp only [mul_add, map_add, hx, hy]; abel
    · intro a y _ hy
      simp only [mul_smul_comm, map_smul, hy, smul_add]

  let E : Fin 2 → Fin 2 → Matrix (Fin 2) (Fin 2) k := fun i j => Matrix.single i j 1
  have hEE : ∀ i j l m : Fin 2, E i j * E l m = if j = l then E i m else 0 := by
    intro i j l m
    by_cases h : j = l
    · subst h; simp [E]
    · simp [E, h]
  have hdiag : ∑ i : Fin 2, E i i = 1 := by
    ext i j
    rw [Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [E, Matrix.single]
  let M : Matrix (Fin 2) (Fin 2) k := ∑ i : Fin 2, D (E i 0) * E 0 i
  have hunit : ∀ p q : Fin 2, D (E p q) = M * E p q - E p q * M := by
    intro p q
    have h1 : M * E p q = D (E p 0) * E 0 q := by
      show (∑ i : Fin 2, D (E i 0) * E 0 i) * E p q = D (E p 0) * E 0 q
      rw [Finset.sum_mul]
      simp only [mul_assoc, hEE, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h2 : E p q * M = D (E p 0) * E 0 q - D (E p q) := by
      have hx : ∀ i : Fin 2, E p q * D (E i 0) = D (E p q * E i 0) - D (E p q) * E i 0 := by
        intro i; rw [hder]; abel
      show E p q * (∑ i : Fin 2, D (E i 0) * E 0 i) = D (E p 0) * E 0 q - D (E p q)
      rw [Finset.mul_sum]
      have hterm : ∀ i : Fin 2, E p q * (D (E i 0) * E 0 i) =
          (if q = i then D (E p 0) * E 0 i else 0) - D (E p q) * E i i := by
        intro i
        rw [← mul_assoc, hx, sub_mul, mul_assoc, hEE, hEE]
        by_cases hqi : q = i
        · subst hqi; simp
        · simp [hqi]
      simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum,
        hdiag, mul_one]
    rw [h1, h2]; abel
  have hsE : ∀ (i j : Fin 2) (a : k), Matrix.single i j a = a • E i j := by
    intro i j a; simp [E, Matrix.smul_single]
  have hall : ∀ X : Matrix (Fin 2) (Fin 2) k, D X = M * X - X * M := by
    intro X
    rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsE, map_smul, hunit, smul_sub, smul_mul_assoc, mul_smul_comm]
  refine ⟨-M, fun g => ?_⟩
  rw [← hDρ, hall, Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
  abel

end E1

private theorem exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0) :
    ∃ (n : ℕ) (e : W ≃ₗ[k] (Fin n → (Fin 2 → k))),
      ∀ (g : G) (w : W) (i : Fin n), e (σW g w) i = (ρ g).mulVec (e w i) := by
  classical

  have _ := h2

  let L : (G →₀ k) →ₗ[k] Matrix (Fin 2) (Fin 2) k := Finsupp.linearCombination k (fun g => ρ g)
  let Δ : (G →₀ k) →ₗ[k] (W →ₗ[k] W) :=
    Finsupp.linearCombination k (fun g => (σW g : W →ₗ[k] W))
  have hLsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    show LinearMap.range (Finsupp.linearCombination k (fun g => ρ g)) = ⊤
    rw [Finsupp.range_linearCombination, hirr]
  have hker : LinearMap.ker L ≤ LinearMap.ker Δ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    show Finsupp.linearCombination k (fun g => (σW g : W →ₗ[k] W)) c = 0
    rw [Finsupp.linearCombination_apply]
    refine relations_lift ρ σW hirr hann c ?_
    have : Finsupp.linearCombination k (fun g => ρ g) c = 0 := hc
    rwa [Finsupp.linearCombination_apply] at this
  let D : Matrix (Fin 2) (Fin 2) k →ₗ[k] (W →ₗ[k] W) :=
    (LinearMap.ker L).liftQ Δ hker ∘ₗ (L.quotKerEquivOfSurjective hLsurj).symm.toLinearMap
  have hDL : ∀ c, D (L c) = Δ c := by
    intro c
    show (LinearMap.ker L).liftQ Δ hker ((L.quotKerEquivOfSurjective hLsurj).symm (L c)) = Δ c
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  have hDρ : ∀ g : G, D (ρ g) = (σW g : W →ₗ[k] W) := by
    intro g
    have h1 : L (Finsupp.single g 1) = ρ g := by
      show Finsupp.linearCombination k (fun g => ρ g) (Finsupp.single g 1) = ρ g
      rw [Finsupp.linearCombination_single, one_smul]
    have h2' : Δ (Finsupp.single g 1) = σW g := by
      show Finsupp.linearCombination k (fun g => (σW g : W →ₗ[k] W)) (Finsupp.single g 1) = _
      rw [Finsupp.linearCombination_single, one_smul]
    rw [← h1, hDL, h2']

  have hDmul : ∀ X Z : Matrix (Fin 2) (Fin 2) k, D (X * Z) = D X * D Z := by
    intro X Z
    have hX : X ∈ Submodule.span k (Set.range (fun g : G => ρ g)) := by
      rw [hirr]; exact Submodule.mem_top
    have hZ : Z ∈ Submodule.span k (Set.range (fun g : G => ρ g)) := by
      rw [hirr]; exact Submodule.mem_top
    refine Submodule.span_induction (p := fun Z _ => D (X * Z) = D X * D Z) ?_ ?_ ?_ ?_ hZ
    · rintro _ ⟨h, rfl⟩
      refine Submodule.span_induction (p := fun X _ => D (X * ρ h) = D X * D (ρ h)) ?_ ?_ ?_ ?_ hX
      · rintro _ ⟨g, rfl⟩
        rw [← map_mul, hDρ, hDρ, hDρ, ← map_mul σW]
      · simp
      · intro x y _ _ hx hy
        simp only [add_mul, map_add, hx, hy]
      · intro a x _ hx
        simp only [smul_mul_assoc, map_smul, hx]
    · simp
    · intro x y _ _ hx hy
      simp only [mul_add, map_add, hx, hy]
    · intro a y _ hy
      simp only [mul_smul_comm, map_smul, hy]
  have hDone : D 1 = 1 := by
    have := hDρ 1
    rwa [map_one ρ, map_one σW] at this

  let Dring : Matrix (Fin 2) (Fin 2) k →+* Module.End k W :=
    { toFun := D, map_one' := hDone, map_mul' := hDmul,
      map_zero' := D.map_zero, map_add' := D.map_add }
  letI : Module (Matrix (Fin 2) (Fin 2) k) W := Module.compHom W Dring
  have hsmul : ∀ (A : Matrix (Fin 2) (Fin 2) k) (w : W), A • w = D A w := fun A w => rfl
  letI : IsScalarTower k (Matrix (Fin 2) (Fin 2) k) W :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      rw [hsmul, Algebra.algebraMap_eq_smul_one, map_smul, hDone]
      rfl)
  haveI : Module.Finite (Matrix (Fin 2) (Fin 2) k) W :=
    Module.Finite.of_restrictScalars_finite k _ _

  obtain ⟨n, ⟨eM⟩⟩ := Matrix.exists_linearEquiv_fin_fun_of_module (k := k) (W := W)
  refine ⟨n, eM.restrictScalars k, ?_⟩
  intro g w i
  have hσ : σW g w = (ρ g) • w := by rw [hsmul, hDρ]
  show eM (σW g w) i = (ρ g).mulVec (eM w i)
  rw [hσ, Matrix.linearEquiv_matrix_apply_smul]

end Representation

end

#check @Representation.exists_trace_ne_zero
#check @Representation.inv_eq_of_quadratic
#check @Representation.trace_smul_bracket
#check @Representation.relations_lift
#check @Representation.exists_eq_conj_sub_of_cocycle_of_trace_eq_zero
#check @Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation

set_option autoImplicit false
p2m_open "Matrix P2MW.S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation.Matrix"
p2m_open "Representation P2MW.S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation.Representation"

theorem solution
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0) :
    ∃ (n : ℕ) (e : W ≃ₗ[k] (Fin n → (Fin 2 → k))),
      ∀ (g : G) (w : W) (i : Fin n), e (σW g w) i = (ρ g).mulVec (e w i) := by
  exact Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation ρ σW h2 hirr hann

end S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
end P2MW
export P2MW.S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation (solution)
