-- Prove2me | solution 1 for WilliamsonShmoys_planar_maximal_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:09:24.117896+00:00
-- url     : https://prove2.me/submissions/57c5368b-7f5f-49de-9fd1-e11e61d1840c

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_strict_relation_has_maximal__p2m_d8caa262_4f2a_4c35_a872_b5a837a56723_a2
open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    Exists (fun K : SimpleGraph V =>
      And (LE.le G K)
        (And (HasPlanarDrawingOn K)
          (And (K.Connected)
            (forall L : SimpleGraph V, LE.le K L ->
              HasPlanarDrawingOn L -> L = K)))) := by
  classical
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H => And (LE.le G H) (HasPlanarDrawingOn H))
  have hne : s.Nonempty := by
    refine ⟨G, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ G, ⟨le_rfl, hG⟩⟩
  let r : SimpleGraph V -> SimpleGraph V -> Prop :=
    fun A B => And (LE.le A B) (Not (A = B))
  have hirr : forall A : SimpleGraph V, Not (r A A) := by
    intro A h
    exact h.2 rfl
  have htrans : forall A B C : SimpleGraph V, r A B -> r B C -> r A C := by
    intro A B C hAB hBC
    refine ⟨le_trans hAB.1 hBC.1, ?_⟩
    intro hAC
    subst C
    exact hAB.2 (le_antisymm hAB.1 hBC.1)
  obtain ⟨K, hKs, hmax⟩ :=
    finite_strict_relation_has_maximal__p2m_d8caa262_4f2a_4c35_a872_b5a837a56723_a2
      s r hne hirr htrans
  have hKprops : And (LE.le G K) (HasPlanarDrawingOn K) :=
    (Finset.mem_filter.mp hKs).2
  apply Exists.intro K
  apply And.intro hKprops.1
  apply And.intro hKprops.2
  apply And.intro (hconn.mono hKprops.1)
  intro L hKL hLplanar
  have hLs : L ∈ s := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ L, ⟨le_trans hKprops.1 hKL, hLplanar⟩⟩
  by_contra hLK
  exact hmax L hLs (And.intro hKL (Ne.symm hLK))