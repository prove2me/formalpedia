-- Prove2me | solution 1 for TensorNP.Bilinear.AG_feasible_iff_colorable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:59:39.387419+00:00
-- url     : https://prove2.me/submissions/e4ef888a-0a47-4b45-8cc3-7690197d6fe4

import Theorems.Thm_TensorNP_Bilinear_lemma_2_10
import Theorems.Thm_TensorNP_Bilinear_minors_vanish_iff_proportional
import Definitions.Def_TensorNP_Bilinear_Construction
import Definitions.Def_TensorNP_Bilinear_Feasibility

open TensorNP.Bilinear

private lemma minor_count_lower {v : ℕ} (hv : 0 < v) :
    3 ≤ Fintype.card (MinorIdx (2 * v + 1)) := by
  classical
  have hn : 2 < 2 * v + 1 := by omega
  let a : Fin (2 * v + 1) := ⟨0, by omega⟩
  let b : Fin (2 * v + 1) := ⟨1, by omega⟩
  let c : Fin (2 * v + 1) := ⟨2, by omega⟩
  let f : Fin 3 → MinorIdx (2 * v + 1) :=
    ![⟨(a, b), by change (0 : ℕ) < 1; omega⟩,
      ⟨(a, c), by change (0 : ℕ) < 2; omega⟩,
      ⟨(b, c), by change (1 : ℕ) < 2; omega⟩]
  have hf : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [f, a, b, c, Subtype.ext_iff, Prod.ext_iff]
  have h := Fintype.card_le_of_injective f hf
  simpa using h

private lemma slice_count_lower {v : ℕ} (hv : 0 < v) :
    Fintype.card (Fin (2 * v + 1) ⊕ Fin (2 * v + 1)) < Fintype.card (SliceIdx v) := by
  have h := minor_count_lower hv
  simp only [SliceIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

private lemma nonzero_kernel {v : ℕ} (hv : 0 < v)
    (L : (SliceIdx v → ℂ) →ₗ[ℂ] (Fin (2 * v + 1) ⊕ Fin (2 * v + 1) → ℂ)) :
    ∃ x, x ≠ 0 ∧ L x = 0 := by
  have hn : ¬ Function.Injective L := by
    intro hi
    have hdim := LinearMap.finrank_le_finrank_of_injective hi
    simp only [Module.finrank_fintype_fun_eq_card] at hdim
    have h := slice_count_lower hv
    omega
  have hn' : ∃ x y, L x = L y ∧ x ≠ y := by
    by_contra h
    apply hn
    intro x y heq
    by_contra hne
    exact h ⟨x, y, heq, hne⟩
  obtain ⟨x, y, hxy, hne⟩ := hn'
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  simp [map_sub, hxy]

private noncomputable def constraintMap {v : ℕ} (G : SimpleGraph (Fin v))
    (p : Fin (2 * v + 1) → ℂ) :
    (SliceIdx v → ℂ) →ₗ[ℂ] (Fin (2 * v + 1) ⊕ Fin (2 * v + 1) → ℂ) where
  toFun u := Sum.elim
    (fun j ↦ ∑ s, ∑ k, (AG G s j k : ℂ) * u s * p k)
    (fun k ↦ ∑ s, ∑ j, (AG G s j k : ℂ) * u s * p j)
  map_add' u u' := by
    funext x
    cases x <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
      mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    funext x
    cases x <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum, RingHom.id_apply] <;>
      apply Finset.sum_congr rfl <;> intro s _ <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> ring

private lemma exists_slice_weights {v : ℕ} (hv : 0 < v) (G : SimpleGraph (Fin v))
    (p : Fin (2 * v + 1) → ℂ) :
    ∃ u : SliceIdx v → ℂ, u ≠ 0 ∧
      (∀ j, ∑ s, ∑ k, (AG G s j k : ℂ) * u s * p k = 0) ∧
      (∀ k, ∑ s, ∑ j, (AG G s j k : ℂ) * u s * p j = 0) := by
  obtain ⟨u, hu, hL⟩ := nonzero_kernel hv (constraintMap G p)
  refine ⟨u, hu, ?_, ?_⟩
  · intro j
    have := congrFun hL (Sum.inl j)
    simpa [constraintMap] using this
  · intro k
    have := congrFun hL (Sum.inr k)
    simpa [constraintMap] using this

private lemma unit_eval {N : ℕ} (a b : Fin N) (p q : Fin N → ℂ) :
    ∑ j, ∑ k, (unitMat a b j k : ℂ) * p j * q k = p a * q b := by
  classical
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [unitMat]
    · intro j _ hj
      simp [unitMat, hj]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · intro i _ hi
    simp [unitMat, hi]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

private lemma minor_eval {N : ℕ} (ab : MinorIdx N) (p q : Fin N → ℂ) :
    ∑ j, ∑ k, (minorSlice ab j k : ℂ) * p j * q k =
      p ab.1.1 * q ab.1.2 - p ab.1.2 * q ab.1.1 := by
  classical
  simp only [minorSlice, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]
  rw [show (∑ j, ∑ k, ((if j = ab.1.1 ∧ k = ab.1.2 then 1 else 0 : ℤ) : ℂ) * p j * q k) =
      p ab.1.1 * q ab.1.2 from unit_eval _ _ _ _,
      show (∑ j, ∑ k, ((if j = ab.1.2 ∧ k = ab.1.1 then 1 else 0 : ℤ) : ℂ) * p j * q k) =
      p ab.1.2 * q ab.1.1 from unit_eval _ _ _ _]

private lemma cube_slices {v : ℕ} (G : SimpleGraph (Fin v)) (c : Fin 3) (i : Fin v)
    (p : Fin (2*v+1) → ℂ) :
    (∑ j, ∑ k, (AG G (Sum.inr (Sum.inl (c,i))) j k : ℂ) * p j * p k) =
      colorEncoding G (Fin.castSucc c) i p := by
  classical
  fin_cases c <;> simp only [AG, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, unit_eval,
    colorEncoding, Fin.castSucc_mk, pow_two]

private lemma minor_slices {v : ℕ} (G : SimpleGraph (Fin v)) (ab : MinorIdx (2*v+1))
    (p : Fin (2*v+1) → ℂ) :
    (∑ j, ∑ k, (AG G (Sum.inl ab) j k : ℂ) * p j * p k) = 0 := by
  rw [show (∑ j, ∑ k, (AG G (Sum.inl ab) j k : ℂ) * p j * p k) =
    ∑ j, ∑ k, (minorSlice ab j k : ℂ) * p j * p k from rfl, minor_eval]
  ring

private lemma edge_slices {v : ℕ} (G : SimpleGraph (Fin v)) (i : Fin v)
    (p : Fin (2*v+1) → ℂ) :
    (∑ j, ∑ k, (AG G (Sum.inr (Sum.inr i)) j k : ℂ) * p j * p k) =
      colorEncoding G 3 i p := by
  classical
  simp only [AG, colorEncoding, Int.cast_sum, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs with hadj
  · simp only [Int.cast_ite, Int.cast_add, Int.cast_zero, add_mul, zero_mul,
      Finset.sum_add_distrib, unit_eval, pow_two]
  · simp

private lemma scalar_eval {v : ℕ} (G : SimpleGraph (Fin v)) (s : SliceIdx v)
    (c : ℂ) (p : Fin (2 * v + 1) → ℂ) :
    (∑ j, ∑ k, (AG G s j k : ℂ) * (c * p j) * p k) =
      c * (∑ j, ∑ k, (AG G s j k : ℂ) * p j * p k) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem solution {v : ℕ} (G : SimpleGraph (Fin v)) (hv : 0 < v) :
    TBF (fun s p q ↦ (AG G s p q : ℂ)) ↔ G.Colorable 3 := by
  constructor
  · rintro ⟨u, p, q, hu, hp, hq, h1, h2, h3⟩
    have hminor : ∀ ab : MinorIdx (2 * v + 1),
        ∑ j, ∑ k, (minorSlice ab j k : ℂ) * p j * q k = 0 := by
      intro ab
      exact h1 (Sum.inl ab)
    obtain ⟨c, hc⟩ := (minors_vanish_iff_proportional p q hp hq).mp hminor
    have hc0 : c ≠ 0 := by
      intro hc0
      apply hp
      rw [hc, hc0]
      simp
    have hdiag (s : SliceIdx v) :
        (∑ j, ∑ k, (AG G s j k : ℂ) * q j * q k) = 0 := by
      have h := h1 s
      rw [hc] at h
      simp only [Pi.smul_apply, smul_eq_mul, scalar_eval] at h
      exact (mul_eq_zero.mp h).resolve_left hc0
    apply (lemma_2_10 G).mp
    refine ⟨q, hq, ?_⟩
    intro a i
    fin_cases a
    · have h := hdiag (Sum.inr (Sum.inl ((0 : Fin 3), i)))
      rw [cube_slices] at h
      exact h
    · have h := hdiag (Sum.inr (Sum.inl ((1 : Fin 3), i)))
      rw [cube_slices] at h
      exact h
    · have h := hdiag (Sum.inr (Sum.inl ((2 : Fin 3), i)))
      rw [cube_slices] at h
      exact h
    · have h := hdiag (Sum.inr (Sum.inr i))
      rw [edge_slices] at h
      exact h
  · intro hc
    obtain ⟨p, hp, hpolys⟩ := (lemma_2_10 G).mpr hc
    obtain ⟨u, hu, h2, h3⟩ := exists_slice_weights hv G p
    refine ⟨u, p, p, hu, hp, hp, ?_, h2, h3⟩
    intro s
    cases s with
    | inl ab => exact minor_slices G ab p
    | inr other =>
      cases other with
      | inl ci =>
        rcases ci with ⟨c, i⟩
        rw [cube_slices]
        exact hpolys (Fin.castSucc c) i
      | inr i =>
        rw [edge_slices]
        exact hpolys 3 i
