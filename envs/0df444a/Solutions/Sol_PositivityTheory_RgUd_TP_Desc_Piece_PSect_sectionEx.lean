-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.sectionEx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:37:01.514527+00:00
-- url     : https://prove2.me/submissions/12365827-5617-48c5-941a-18f1ddf3fa79

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FieldGen
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FinrankAdjoinPowLe
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fc
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fieldGen
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial
private theorem finrank_adjoin_pow_le {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] (T : Subalgebra k R) (q n : ℕ) (hq : 0 < q) (L : Fin n → R)
    (hL : ∀ i, L i ^ q ∈ T) :
    finrank k (Algebra.adjoin k ((T : Set R) ∪ Set.range L)) ≤ q ^ n * finrank k T := by
  classical
  let G : (Fin n → ℕ) → R := fun e => ∏ i, L i ^ e i
  let Φ : ((Fin n → Fin q) → T) →ₗ[k] R :=
    ∑ e : Fin n → Fin q, (LinearMap.mulRight k (G fun i => (e i : ℕ))) ∘ₗ T.val.toLinearMap ∘ₗ
      LinearMap.proj e
  have hΦ : ∀ f, Φ f = ∑ e : Fin n → Fin q, (f e : R) * G (fun i => (e i : ℕ)) := by
    intro f; simp [Φ, LinearMap.sum_apply]
  have hsingle : ∀ t ∈ T, ∀ e : Fin n → Fin q, t * G (fun i => (e i : ℕ)) ∈ LinearMap.range Φ := by
    intro t ht e
    refine ⟨Pi.single e ⟨t, ht⟩, ?_⟩
    rw [hΦ, Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hA : ∀ t ∈ T, ∀ e : Fin n → ℕ, t * G e ∈ LinearMap.range Φ := by
    intro t ht e
    have hG : G e = (∏ i, (L i ^ q) ^ (e i / q)) *
        G (fun i => ((⟨e i % q, Nat.mod_lt _ hq⟩ : Fin q) : ℕ)) := by
      simp only [G]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hG, ← mul_assoc]
    exact hsingle _ (T.mul_mem ht (T.prod_mem fun i _ => T.pow_mem (hL i) _)) _
  have hLmul : ∀ i e, L i * G e = G (e + Pi.single i 1) := by
    intro i e
    simp only [G, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hclosed : ∀ y ∈ Algebra.adjoin k ((T : Set R) ∪ Set.range L),
      ∀ m ∈ LinearMap.range Φ, y * m ∈ LinearMap.range Φ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rintro m ⟨f, rfl⟩
      rw [hΦ, Finset.mul_sum]
      refine Submodule.sum_mem _ fun e _ => ?_
      rcases hx with hx | ⟨i, rfl⟩
      · rw [← mul_assoc]; exact hsingle _ (T.mul_mem hx (f e).2) e
      · rw [mul_left_comm, hLmul]; exact hA _ (f e).2 _
    | algebraMap a =>
      intro m hm; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ a hm
    | add x y _ _ hx hy =>
      intro m hm; rw [add_mul]; exact add_mem (hx m hm) (hy m hm)
    | mul x y _ _ hx hy =>
      intro m hm; rw [mul_assoc]; exact hx _ (hy m hm)
  have h1 : (1 : R) ∈ LinearMap.range Φ := by
    have := hA 1 T.one_mem 0
    simpa [G] using this
  have hle : Subalgebra.toSubmodule (Algebra.adjoin k ((T : Set R) ∪ Set.range L)) ≤
      LinearMap.range Φ := by
    intro y hy
    simpa using hclosed y hy 1 h1
  calc finrank k (Algebra.adjoin k ((T : Set R) ∪ Set.range L))
      = finrank k (Subalgebra.toSubmodule (Algebra.adjoin k ((T : Set R) ∪ Set.range L))) :=
        (Subalgebra.finrank_toSubmodule _).symm
    _ ≤ finrank k (LinearMap.range Φ) := Submodule.finrank_mono hle
    _ ≤ finrank k ((Fin n → Fin q) → T) := LinearMap.finrank_range_le Φ
    _ = q ^ n * finrank k T := by simp [Module.finrank_pi_fintype]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {k R : Type*} [Field k] [CommRing R] [Algebra k R] [FiniteDimensional k R]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hnil : ∀ r : R, IsNilpotent r → r ^ (p ^ c) = 0)
    (hroot : ∀ a : k, ∃ w : R, w ^ (p ^ c) = algebraMap k R a) :
    ∃ S : Subalgebra k R, (∀ s ∈ S, IsNilpotent s → s = 0) ∧ ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s) := by
  classical
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨⊤, fun s _ hs => by simpa using hnil s hs, fun r => ⟨r, Algebra.mem_top, by simp⟩⟩
  have hq2 : 2 ≤ p ^ c := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hc.ne' p)
  have hq0 : 0 < p ^ c := by omega
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let N := nilradical R
  let f : R →ₐ[k] R ⧸ N := Ideal.Quotient.mkₐ k N
  have hf : ∀ r, f r = Ideal.Quotient.mk N r := fun r => rfl
  have hfN : ∀ r, f r = 0 ↔ IsNilpotent r := fun r => by
    rw [hf, Ideal.Quotient.eq_zero_iff_mem]; exact mem_nilradical
  haveI : IsReduced (R ⧸ N) :=
    (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical _)
  haveI : FiniteDimensional k (R ⧸ N) :=
    Module.Finite.of_surjective f.toLinearMap Ideal.Quotient.mk_surjective
  have hrootbar : ∀ a : k, ∃ w : R ⧸ N, w ^ (p ^ c) = algebraMap k (R ⧸ N) a := fun a => by
    obtain ⟨w, hw⟩ := hroot a
    exact ⟨f w, by rw [← map_pow, hw, AlgHom.commutes]⟩

  obtain ⟨n, hn, -⟩ := fieldGen (k := k) (E := Tw k p c) p c
    (fun a => ⟨(a : k), rfl⟩)

  have hα : ∀ I : MaximalSpectrum R, ∃ α : Fin n → R ⧸ I.asIdeal,
      Algebra.adjoin k (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
    intro I
    haveI := I.isMaximal
    letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional k (R ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    obtain ⟨n', hn', α, hα⟩ := fieldGen (k := k) (E := R ⧸ I.asIdeal) p c (fun a => by
      obtain ⟨w, hw⟩ := hroot a
      exact ⟨Ideal.Quotient.mkₐ k I.asIdeal w, by rw [← map_pow, hw, AlgHom.commutes]⟩)
    have : n' = n := Nat.pow_right_injective hq2 (hn'.symm.trans hn)
    subst this
    exact ⟨α, hα⟩
  choose α hα using hα
  let π : (R ⧸ N) ≃ₐ[k] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal :=
    (IsArtinianRing.quotNilradicalEquivPi R).restrictScalars k
  let Lbar : Fin n → R ⧸ N := fun i => π.symm (fun I => α I i)
  let σ : ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal → R ⧸ N := fun I z => π.symm (Pi.single I z)
  have hσadd : ∀ I z w, σ I (z + w) = σ I z + σ I w := fun I z w => by
    simp only [σ, Pi.single_add, map_add]
  have hσmul : ∀ I z w, σ I (z * w) = σ I z * σ I w := fun I z w => by
    simp only [σ, Pi.single_mul, map_mul]
  have hσpow : ∀ I z, σ I (z ^ (p ^ c)) = σ I z ^ (p ^ c) := fun I z => by
    apply π.injective
    simp only [σ, map_pow, AlgEquiv.apply_symm_apply]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h, zero_pow hq0.ne']
  have hσalg : ∀ I (a : k), σ I (algebraMap k _ a) = algebraMap k (R ⧸ N) a * σ I 1 := fun I a => by
    apply π.injective
    simp only [σ, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h]
  have hσL : ∀ I i, σ I (α I i) = σ I 1 * Lbar i := fun I i => by
    apply π.injective
    simp only [σ, Lbar, map_mul, AlgEquiv.apply_symm_apply]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h]
  let A := Algebra.adjoin k (Set.range (fun b : R ⧸ N => b ^ (p ^ c)) ∪ Set.range Lbar)
  have he : ∀ I, σ I 1 ∈ A := fun I => by
    have : σ I 1 = σ I 1 ^ (p ^ c) := by rw [← hσpow, one_pow]
    rw [this]; exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
  have hσA : ∀ I z, σ I z ∈ A := by
    intro I z
    have hz : z ∈ Algebra.adjoin k
        (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range (α I)) := by
      rw [hα I]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨i, rfl⟩
      · rw [hσpow]; exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
      · rw [hσL]; exact A.mul_mem (he I) (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    | algebraMap a => rw [hσalg]; exact A.mul_mem (A.algebraMap_mem a) (he I)
    | add x y _ _ hx hy => rw [hσadd]; exact A.add_mem hx hy
    | mul x y _ _ hx hy => rw [hσmul]; exact A.mul_mem hx hy
  have hAtop : ∀ x : R ⧸ N, x ∈ A := by
    intro x
    have : x = ∑ I, σ I (π x I) := by
      apply π.injective
      rw [map_sum]
      simp only [σ, AlgEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single (π x)).symm
    rw [this]; exact A.sum_mem fun I _ => hσA I _

  choose L hL using fun i => Ideal.Quotient.mk_surjective (I := N) (Lbar i)
  let T := Pw k R (p ^ c)
  have hLq : ∀ i, L i ^ (p ^ c) ∈ T := fun i => Algebra.subset_adjoin ⟨L i, rfl⟩
  let S := Algebra.adjoin k ((T : Set R) ∪ Set.range L)
  have hAS : A ≤ S.map f := Algebra.adjoin_le (by
    rintro _ (⟨b, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨r ^ (p ^ c), Algebra.subset_adjoin (Or.inl (Algebra.subset_adjoin ⟨r, rfl⟩)),
        by rw [map_pow]; rfl⟩
    · exact ⟨L i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩), hL i⟩)
  have hlift : ∀ r : R, ∃ s ∈ S, f s = f r := fun r => hAS (hAtop (f r))

  let g : S →ₗ[k] R ⧸ N := f.toLinearMap ∘ₗ S.val.toLinearMap
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs, hfs⟩ := hlift r
    exact ⟨⟨s, hs⟩, hfs⟩
  have hS : finrank k S ≤ (p ^ c) ^ n * finrank k T :=
    finrank_adjoin_pow_le T (p ^ c) n hq0 L hLq
  have hTmem : ∀ t : T, f t ∈ Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c)) := by
    intro t
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).mp t.2
    show f t ∈ Pw k (R ⧸ N) (p ^ c)
    rw [← hw, map_pow]
    exact Algebra.subset_adjoin ⟨f w, rfl⟩
  let h : T →ₗ[k] Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c)) :=
    LinearMap.codRestrict _ (f.toLinearMap ∘ₗ T.val.toLinearMap) hTmem
  have hinj : Function.Injective h := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h0 : f t = 0 := congrArg Subtype.val ht
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).mp t.2
    obtain ⟨m, hm⟩ := (hfN _).mp h0
    have hwn : IsNilpotent w := ⟨p ^ c * m, by rw [pow_mul, hw, hm]⟩
    exact Subtype.ext (by rw [← hw, hnil w hwn]; rfl)
  have hT : finrank k T ≤ finrank k (Pw k (R ⧸ N) (p ^ c)) := by
    rw [← Subalgebra.finrank_toSubmodule (Pw k (R ⧸ N) (p ^ c))]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hfc := fc (B := R ⧸ N) p c hrootbar
  rw [hn] at hfc
  have hbar : finrank k (R ⧸ N) ≤ finrank k S := by
    rw [← finrank_top k (R ⧸ N), ← LinearMap.range_eq_top.mpr hg]
    exact LinearMap.finrank_range_le g
  have heq : finrank k S = finrank k (R ⧸ N) := by
    refine le_antisymm ?_ hbar
    calc finrank k S ≤ (p ^ c) ^ n * finrank k T := hS
      _ ≤ (p ^ c) ^ n * finrank k (Pw k (R ⧸ N) (p ^ c)) := Nat.mul_le_mul_left _ hT
      _ = finrank k (R ⧸ N) := hfc.symm
  have hginj : Function.Injective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hg
  refine ⟨S, fun s hs hsn => ?_, fun r => ?_⟩
  · have : g ⟨s, hs⟩ = g 0 := by
      rw [map_zero]; exact (hfN s).mpr hsn
    exact congrArg Subtype.val (hginj this)
  · obtain ⟨s, hs, hfs⟩ := hlift r
    refine ⟨s, hs, (hfN _).mp ?_⟩
    rw [map_sub, hfs, sub_self]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
