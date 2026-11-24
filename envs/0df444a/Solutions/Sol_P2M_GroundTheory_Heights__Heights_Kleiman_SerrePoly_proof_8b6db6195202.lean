-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SerrePoly_proof_8b6db6195202
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:01.563967+00:00
-- url     : https://prove2.me/submissions/661b1c0d-deb6-4d81-92d0-be6fac21367c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SerrePoly
theorem _root_.solution (hL : SerrePoly.Laurent.Statement.{u}) (hT : Cech.Transport.Statement.{u, u, u})
    (hC : SerrePoly.LaurentCohom.Statement.{u}) : SerrePoly.Statement.{u} := by
  intro S _ _ N
  obtain ⟨hinj, hpiece, ι, hι, hres, hmk, hdeg⟩ := hL S N
  obtain ⟨hfin, hvan, hconst⟩ := hC S N
  have hφ : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N (Poly S N) I.1),
      ι J (locResS I J h m) = Cech.idRes S (Laurent S N) Finset.univ I J h (ι I m) :=
    fun I J h m => hres I J h m
  have hd : ∀ (c : ℤ) (I : StdCell N) (m : LocMod S N (Poly S N) I.1),
      m ∈ degLoc (polyGraded S N) c I → ι I m ∈ laurentDeg S N c I := fun c I m hm => by
    rw [← hdeg c I]; exact Submodule.mem_map_of_mem hm
  have hb : ∀ (i : ℕ) (c : ℤ), Function.Bijective
      (Cech.mapHdeg (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ (hd c) i) :=
    fun i c => hT (N + 1) Finset.univ S _ _ _ _ (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ
      (hd c) hι (hdeg c) i
  let E : ∀ (i : ℕ) (c : ℤ), cohom (polyGraded S N) i c ≃ₗ[S] laurentCohom S N i c :=
    fun i c => LinearEquiv.ofBijective _ (hb i c)
  refine ⟨fun i c => Module.Finite.equiv (E i c).symm, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have := hvan c hc i hi
    exact (E i c).toEquiv.subsingleton
  ·
    intro m m' hmm
    have h0 : (constCochain (S := S) (N := N) (M := Poly S N) (m : Poly S N)) =
        constCochain (S := S) (N := N) (M := Poly S N) (m' : Poly S N) := by
      have hmem := (Submodule.Quotient.eq _).mp hmm
      change _ ∈ (⊥ : Submodule S _).comap _ at hmem
      rw [Submodule.mem_comap, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    let I0 : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{0}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    have h1 := congrArg (ι I0.1) (congrFun h0 I0)
    change ι I0.1 (locMk (Poly S N) I0.1.1 m) = ι I0.1 (locMk (Poly S N) I0.1.1 m') at h1
    rw [hmk, hmk] at h1
    exact Subtype.ext (hinj h1)
  ·
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hw : (Cech.mapC ι 0 (z : Cech.Cochain (locSys S N (Poly S N)) 0)) ∈
        Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
          (Cech.idRes S (Laurent S N) Finset.univ) 0 := by
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, fun I _ => ?_⟩
      · rw [← Cech.mapC_d ι hφ, LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1, map_zero]
      · exact hd c I.1 _ ((Submodule.mem_inf.mp z.2).2 I (Set.mem_univ _))
    obtain ⟨f, hf, hzf⟩ := hconst c hc _ hw
    rw [← hpiece c] at hf
    obtain ⟨m, hm, rfl⟩ := hf
    refine ⟨⟨m, hm⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext I
    apply hι I.1
    change ι I.1 (locMk (Poly S N) I.1.1 m) = _
    rw [hmk]
    exact (hzf I).symm
end SerrePoly
end GroundTheory.Heights₂.Heights.Kleiman
